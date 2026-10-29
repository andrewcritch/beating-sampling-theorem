import BstLean.Part266Shard9Step4


/-! A coarse bound on the actual paper statistics constant at dimension 12575. -/
namespace BstLean.Part266.Row12575
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12573 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12573 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12573 128 ≤ (12827 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12827 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12575) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12575 : ℕ))
    (by norm_num : (12575 : ℕ) ≤ 16384)
  have ht : paperTail256 12575 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12575 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12575 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12575 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12575 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12575 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12573 128 * √(2 / (12575 : ℝ)) *
      (√(12575 : ℝ) + paperT0 12575 + paperTail256 12575) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12575 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12575 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12575 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12573 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12573 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12575 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12575

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12575
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12575 (61 / 100) 162 (17 / (100 * 12575)) (26 / (10 * 12575)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12575 (61 / 100) 162 (17 / (100 * 12575)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (30681383 / 6250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (48797429 / 31250000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2770270767 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12575 / 12575 * (61 / 100)) ^ 4 * inverseRadius8 (12575 - 1) /
            envelopeGap 12575 (61 / 100) 162 (17 / (100 * 12575)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12575

namespace BstLean.Part266.Row12575
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12575 162 ≤ (4697445813 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12575 162 ≤ (313429467 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (75332879 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12575 162 ≤ (94420789 / 5000000000000000000)
  w1 : (tableEnvelope C).w1 12575 162 ≤ (671785841 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12575 162 ≤ (61363437 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (30681383 / 6250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (30681383 / 6250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (48797429 / 31250000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2770270767 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3676803 / 1000000000) : ℝ) ≤ √(17 / (100 * 12575) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12575) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (17725049 / 8000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9879010983 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12575) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12575) ≤ (14057789 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12575) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12575 * (162 : ℝ) ^ 2 + 26 / (10 * 12575) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12575) : ℝ)) (tA 12575 * 162 ^ 2 + 26 / (10 * 12575)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3676803 / 1000000000))) * ((30681383 / 6250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3676803 / 1000000000)) ^ 3) * ((48797429 / 31250000000000000000000))) + ((2770270767 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3676803 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12575) : ℝ)) d.D d.V d.P (√(tA 12575) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3676803 / 1000000000)) ^ 2 * (((17725049 / 8000000000000)) * ((9879010983 / 250000000000000000)))) + ((2770270767 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12575) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3676803 / 1000000000)) * ((30681383 / 6250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12575) : ℝ)) (tA 12575 * 162 ^ 2 + 26 / (10 * 12575)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((30681383 / 6250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3676803 / 1000000000)) ^ 2) * ((48797429 / 31250000000000000000000)) + ((2770270767 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12575) : ℝ)) (√(26 / (10 * 12575) : ℝ)) d.D d.V d.P (√(tA 12575) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3676803 / 1000000000)) * (((17725049 / 8000000000000)) * ((9879010983 / 250000000000000000))) + ((2770270767 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12575) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((30681383 / 6250000000000000000) : ℝ) + ((2770270767 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12575

namespace BstLean.Part266.Row12575
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12575 162 ∧
    0 ≤ (tableEnvelope C).f1 12575 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12575 162 ∧
    0 ≤ (tableEnvelope C).w1 12575 162 ∧ 0 ≤ (tableEnvelope C).w2 12575 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12575 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12575 162 ∧ 0 ≤ d.f1 12575 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12575 162 ∧ 0 ≤ d.w1 12575 162 ∧ 0 ≤ d.w2 12575 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12575 ≤ 2 * (228 / 100 : ℝ) / 12575 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12575 ≤ 2 * (370 / 100 : ℝ) / 12575 := by
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
    (completeRAData (tableEnvelope C) 12575 162).locationBound 12575 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12575 162).energyBound 12575 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12575 162) (d.f1 12575 162) d.f2 ≤
      32 * (((4697445813 / 1000000000000000000) : ℝ) + (313429467 / 200000000000000000) + (75332879 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12575 162) (d.w1 12575 162)
      (d.w2 12575 162) ≤
      32 * (((94420789 / 5000000000000000000) : ℝ) + (671785841 / 50000000000000000000) + (61363437 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12575 162) (d.f1 12575 162) d.f2 ≤
      ((4697445813 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4697445813 / 1000000000000000000)) * ((313429467 / 200000000000000000)) * (126 / 100) +
      2 * (((313429467 / 200000000000000000)) ^ 2 + 2 * ((4697445813 / 1000000000000000000)) * ((75332879 / 200000000000000000))) +
      6 * ((313429467 / 200000000000000000)) * ((75332879 / 200000000000000000)) * (126 / 100) + 8 * ((75332879 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12575 162) (d.f1 12575 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12575 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12575 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12575 162) (d.f1 12575 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12575 162) (d.w1 12575 162) (d.w2 12575 162)
  have hwexpr0 : 0 ≤ d.w0 12575 162 + d.w1 12575 162 * √(π / 2) +
      2 * d.w2 12575 162 + energyR16 12575 *
      radiusPolynomialRoot16 (d.w0 12575 162) (d.w1 12575 162) (d.w2 12575 162) := by
    positivity
  constructor
  · change (12575 : ℝ) ^ 8 * (mA 12575 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12575 162) (d.f1 12575 162) d.f2 + locationR16 12575 *
        radiusPolynomialRoot16 (d.f0 12575 162) (d.f1 12575 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12575 : ℝ) ^ 8 * (mA 12575 : ℝ) ^ 8 *
        ((((4697445813 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4697445813 / 1000000000000000000)) * ((313429467 / 200000000000000000)) * (126 / 100) +
          2 * (((313429467 / 200000000000000000)) ^ 2 + 2 * ((4697445813 / 1000000000000000000)) * ((75332879 / 200000000000000000))) +
          6 * ((313429467 / 200000000000000000)) * ((75332879 / 200000000000000000)) * (126 / 100) + 8 * ((75332879 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12575) *
          (32 * (((4697445813 / 1000000000000000000) : ℝ) + (313429467 / 200000000000000000) + (75332879 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12575 : ℝ) ^ 16 *
      (d.w0 12575 162 + d.w1 12575 162 * √(π / 2) + 2 * d.w2 12575 162 +
        energyR16 12575 * radiusPolynomialRoot16 (d.w0 12575 162) (d.w1 12575 162)
          (d.w2 12575 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12575 : ℝ) ^ 16 *
        (((94420789 / 5000000000000000000) : ℝ) + ((671785841 / 50000000000000000000)) * (126 / 100) + 2 * ((61363437 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12575) *
          (32 * (((94420789 / 5000000000000000000) : ℝ) + (671785841 / 50000000000000000000) + (61363437 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12575

/-! A coarse bound on the actual paper statistics constant at dimension 12576. -/
namespace BstLean.Part266.Row12576
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12574 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12574 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12574 128 ≤ (12828 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12828 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12576) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12576 : ℕ))
    (by norm_num : (12576 : ℕ) ≤ 16384)
  have ht : paperTail256 12576 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12576 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12576 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12576 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12576 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12576 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12574 128 * √(2 / (12576 : ℝ)) *
      (√(12576 : ℝ) + paperT0 12576 + paperTail256 12576) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12576 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12576 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12576 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12574 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12574 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12576 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12576

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12576
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12576 (61 / 100) 162 (17 / (100 * 12576)) (26 / (10 * 12576)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12576 (61 / 100) 162 (17 / (100 * 12576)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (490785027 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1561021101 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1384245857 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12576 / 12576 * (61 / 100)) ^ 4 * inverseRadius8 (12576 - 1) /
            envelopeGap 12576 (61 / 100) 162 (17 / (100 * 12576)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12576

namespace BstLean.Part266.Row12576
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12576 162 ≤ (4696511309 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12576 162 ≤ (1566835639 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (188294749 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12576 162 ≤ (1887965169 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12576 162 ≤ (671625557 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12576 162 ≤ (490790391 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (490785027 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (490785027 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1561021101 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1384245857 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3676657 / 1000000000) : ℝ) ≤ √(17 / (100 * 12576) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12576) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (34615107 / 15625000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39509759567 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12576) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12576) ≤ (112453369 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12576) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12576 * (162 : ℝ) ^ 2 + 26 / (10 * 12576) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12576) : ℝ)) (tA 12576 * 162 ^ 2 + 26 / (10 * 12576)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3676657 / 1000000000))) * ((490785027 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3676657 / 1000000000)) ^ 3) * ((1561021101 / 1000000000000000000000000))) + ((1384245857 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3676657 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12576) : ℝ)) d.D d.V d.P (√(tA 12576) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3676657 / 1000000000)) ^ 2 * (((34615107 / 15625000000000)) * ((39509759567 / 1000000000000000000)))) + ((1384245857 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12576) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3676657 / 1000000000)) * ((490785027 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12576) : ℝ)) (tA 12576 * 162 ^ 2 + 26 / (10 * 12576)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((490785027 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3676657 / 1000000000)) ^ 2) * ((1561021101 / 1000000000000000000000000)) + ((1384245857 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12576) : ℝ)) (√(26 / (10 * 12576) : ℝ)) d.D d.V d.P (√(tA 12576) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3676657 / 1000000000)) * (((34615107 / 15625000000000)) * ((39509759567 / 1000000000000000000))) + ((1384245857 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12576) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((490785027 / 100000000000000000000) : ℝ) + ((1384245857 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12576

namespace BstLean.Part266.Row12576
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12576 162 ∧
    0 ≤ (tableEnvelope C).f1 12576 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12576 162 ∧
    0 ≤ (tableEnvelope C).w1 12576 162 ∧ 0 ≤ (tableEnvelope C).w2 12576 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12576 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12576 162 ∧ 0 ≤ d.f1 12576 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12576 162 ∧ 0 ≤ d.w1 12576 162 ∧ 0 ≤ d.w2 12576 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12576 ≤ 2 * (228 / 100 : ℝ) / 12576 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12576 ≤ 2 * (370 / 100 : ℝ) / 12576 := by
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
    (completeRAData (tableEnvelope C) 12576 162).locationBound 12576 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12576 162).energyBound 12576 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12576 162) (d.f1 12576 162) d.f2 ≤
      32 * (((4696511309 / 1000000000000000000) : ℝ) + (1566835639 / 1000000000000000000) + (188294749 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12576 162) (d.w1 12576 162)
      (d.w2 12576 162) ≤
      32 * (((1887965169 / 100000000000000000000) : ℝ) + (671625557 / 50000000000000000000) + (490790391 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12576 162) (d.f1 12576 162) d.f2 ≤
      ((4696511309 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4696511309 / 1000000000000000000)) * ((1566835639 / 1000000000000000000)) * (126 / 100) +
      2 * (((1566835639 / 1000000000000000000)) ^ 2 + 2 * ((4696511309 / 1000000000000000000)) * ((188294749 / 500000000000000000))) +
      6 * ((1566835639 / 1000000000000000000)) * ((188294749 / 500000000000000000)) * (126 / 100) + 8 * ((188294749 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12576 162) (d.f1 12576 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12576 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12576 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12576 162) (d.f1 12576 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12576 162) (d.w1 12576 162) (d.w2 12576 162)
  have hwexpr0 : 0 ≤ d.w0 12576 162 + d.w1 12576 162 * √(π / 2) +
      2 * d.w2 12576 162 + energyR16 12576 *
      radiusPolynomialRoot16 (d.w0 12576 162) (d.w1 12576 162) (d.w2 12576 162) := by
    positivity
  constructor
  · change (12576 : ℝ) ^ 8 * (mA 12576 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12576 162) (d.f1 12576 162) d.f2 + locationR16 12576 *
        radiusPolynomialRoot16 (d.f0 12576 162) (d.f1 12576 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12576 : ℝ) ^ 8 * (mA 12576 : ℝ) ^ 8 *
        ((((4696511309 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4696511309 / 1000000000000000000)) * ((1566835639 / 1000000000000000000)) * (126 / 100) +
          2 * (((1566835639 / 1000000000000000000)) ^ 2 + 2 * ((4696511309 / 1000000000000000000)) * ((188294749 / 500000000000000000))) +
          6 * ((1566835639 / 1000000000000000000)) * ((188294749 / 500000000000000000)) * (126 / 100) + 8 * ((188294749 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12576) *
          (32 * (((4696511309 / 1000000000000000000) : ℝ) + (1566835639 / 1000000000000000000) + (188294749 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12576 : ℝ) ^ 16 *
      (d.w0 12576 162 + d.w1 12576 162 * √(π / 2) + 2 * d.w2 12576 162 +
        energyR16 12576 * radiusPolynomialRoot16 (d.w0 12576 162) (d.w1 12576 162)
          (d.w2 12576 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12576 : ℝ) ^ 16 *
        (((1887965169 / 100000000000000000000) : ℝ) + ((671625557 / 50000000000000000000)) * (126 / 100) + 2 * ((490790391 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12576) *
          (32 * (((1887965169 / 100000000000000000000) : ℝ) + (671625557 / 50000000000000000000) + (490790391 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12576

/-! A coarse bound on the actual paper statistics constant at dimension 12577. -/
namespace BstLean.Part266.Row12577
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12575 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12575 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12575 128 ≤ (12829 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12829 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12577) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12577 : ℕ))
    (by norm_num : (12577 : ℕ) ≤ 16384)
  have ht : paperTail256 12577 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12577 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12577 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12577 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12577 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12577 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12575 128 * √(2 / (12577 : ℝ)) *
      (√(12577 : ℝ) + paperT0 12577 + paperTail256 12577) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12577 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12577 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12577 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12575 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12575 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12577 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12577

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12577
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12577 (61 / 100) 162 (17 / (100 * 12577)) (26 / (10 * 12577)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12577 (61 / 100) 162 (17 / (100 * 12577)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (490667963 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (12191599 / 7812500000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1106685579 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12577 / 12577 * (61 / 100)) ^ 4 * inverseRadius8 (12577 - 1) /
            envelopeGap 12577 (61 / 100) 162 (17 / (100 * 12577)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12577

namespace BstLean.Part266.Row12577
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12577 162 ≤ (1173894283 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12577 162 ≤ (783262023 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (5883041 / 15625000000000000)
  w0 : (tableEnvelope C).w0 12577 162 ≤ (943757357 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12577 162 ≤ (671465327 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12577 162 ≤ (122668331 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (490667963 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (490667963 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (12191599 / 7812500000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1106685579 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3676511 / 1000000000) : ℝ) ≤ √(17 / (100 * 12577) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12577) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2215102623 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9875869177 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12577) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12577) ≤ (28111107 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12577) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12577 * (162 : ℝ) ^ 2 + 26 / (10 * 12577) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12577) : ℝ)) (tA 12577 * 162 ^ 2 + 26 / (10 * 12577)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3676511 / 1000000000))) * ((490667963 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3676511 / 1000000000)) ^ 3) * ((12191599 / 7812500000000000000000))) + ((1106685579 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3676511 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12577) : ℝ)) d.D d.V d.P (√(tA 12577) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3676511 / 1000000000)) ^ 2 * (((2215102623 / 1000000000000000)) * ((9875869177 / 250000000000000000)))) + ((1106685579 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12577) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3676511 / 1000000000)) * ((490667963 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12577) : ℝ)) (tA 12577 * 162 ^ 2 + 26 / (10 * 12577)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((490667963 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3676511 / 1000000000)) ^ 2) * ((12191599 / 7812500000000000000000)) + ((1106685579 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12577) : ℝ)) (√(26 / (10 * 12577) : ℝ)) d.D d.V d.P (√(tA 12577) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3676511 / 1000000000)) * (((2215102623 / 1000000000000000)) * ((9875869177 / 250000000000000000))) + ((1106685579 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12577) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((490667963 / 100000000000000000000) : ℝ) + ((1106685579 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12577

namespace BstLean.Part266.Row12577
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12577 162 ∧
    0 ≤ (tableEnvelope C).f1 12577 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12577 162 ∧
    0 ≤ (tableEnvelope C).w1 12577 162 ∧ 0 ≤ (tableEnvelope C).w2 12577 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12577 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12577 162 ∧ 0 ≤ d.f1 12577 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12577 162 ∧ 0 ≤ d.w1 12577 162 ∧ 0 ≤ d.w2 12577 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12577 ≤ 2 * (228 / 100 : ℝ) / 12577 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12577 ≤ 2 * (370 / 100 : ℝ) / 12577 := by
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
    (completeRAData (tableEnvelope C) 12577 162).locationBound 12577 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12577 162).energyBound 12577 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12577 162) (d.f1 12577 162) d.f2 ≤
      32 * (((1173894283 / 250000000000000000) : ℝ) + (783262023 / 500000000000000000) + (5883041 / 15625000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12577 162) (d.w1 12577 162)
      (d.w2 12577 162) ≤
      32 * (((943757357 / 50000000000000000000) : ℝ) + (671465327 / 50000000000000000000) + (122668331 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12577 162) (d.f1 12577 162) d.f2 ≤
      ((1173894283 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1173894283 / 250000000000000000)) * ((783262023 / 500000000000000000)) * (126 / 100) +
      2 * (((783262023 / 500000000000000000)) ^ 2 + 2 * ((1173894283 / 250000000000000000)) * ((5883041 / 15625000000000000))) +
      6 * ((783262023 / 500000000000000000)) * ((5883041 / 15625000000000000)) * (126 / 100) + 8 * ((5883041 / 15625000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12577 162) (d.f1 12577 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12577 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12577 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12577 162) (d.f1 12577 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12577 162) (d.w1 12577 162) (d.w2 12577 162)
  have hwexpr0 : 0 ≤ d.w0 12577 162 + d.w1 12577 162 * √(π / 2) +
      2 * d.w2 12577 162 + energyR16 12577 *
      radiusPolynomialRoot16 (d.w0 12577 162) (d.w1 12577 162) (d.w2 12577 162) := by
    positivity
  constructor
  · change (12577 : ℝ) ^ 8 * (mA 12577 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12577 162) (d.f1 12577 162) d.f2 + locationR16 12577 *
        radiusPolynomialRoot16 (d.f0 12577 162) (d.f1 12577 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12577 : ℝ) ^ 8 * (mA 12577 : ℝ) ^ 8 *
        ((((1173894283 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1173894283 / 250000000000000000)) * ((783262023 / 500000000000000000)) * (126 / 100) +
          2 * (((783262023 / 500000000000000000)) ^ 2 + 2 * ((1173894283 / 250000000000000000)) * ((5883041 / 15625000000000000))) +
          6 * ((783262023 / 500000000000000000)) * ((5883041 / 15625000000000000)) * (126 / 100) + 8 * ((5883041 / 15625000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12577) *
          (32 * (((1173894283 / 250000000000000000) : ℝ) + (783262023 / 500000000000000000) + (5883041 / 15625000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12577 : ℝ) ^ 16 *
      (d.w0 12577 162 + d.w1 12577 162 * √(π / 2) + 2 * d.w2 12577 162 +
        energyR16 12577 * radiusPolynomialRoot16 (d.w0 12577 162) (d.w1 12577 162)
          (d.w2 12577 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12577 : ℝ) ^ 16 *
        (((943757357 / 50000000000000000000) : ℝ) + ((671465327 / 50000000000000000000)) * (126 / 100) + 2 * ((122668331 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12577) *
          (32 * (((943757357 / 50000000000000000000) : ℝ) + (671465327 / 50000000000000000000) + (122668331 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12577

/-! A coarse bound on the actual paper statistics constant at dimension 12578. -/
namespace BstLean.Part266.Row12578
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12576 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12576 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12576 128 ≤ (12830 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12830 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12578) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12578 : ℕ))
    (by norm_num : (12578 : ℕ) ≤ 16384)
  have ht : paperTail256 12578 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12578 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12578 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12578 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12578 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12578 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12576 128 * √(2 / (12578 : ℝ)) *
      (√(12578 : ℝ) + paperT0 12578 + paperTail256 12578) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12578 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12578 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12578 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12576 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12576 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12578 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12578

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12578
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12578 (61 / 100) 162 (17 / (100 * 12578)) (26 / (10 * 12578)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12578 (61 / 100) 162 (17 / (100 * 12578)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (61318867 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1560028441 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5529874933 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12578 / 12578 * (61 / 100)) ^ 4 * inverseRadius8 (12578 - 1) /
            envelopeGap 12578 (61 / 100) 162 (17 / (100 * 12578)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12578

namespace BstLean.Part266.Row12578
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12578 162 ≤ (58683041 / 12500000000000000)
  f1 : (tableEnvelope C).f1 12578 162 ≤ (783106277 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (94109943 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12578 162 ≤ (1887064417 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12578 162 ≤ (1342610303 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12578 162 ≤ (490556293 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (61318867 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (61318867 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1560028441 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5529874933 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((735273 / 200000000) : ℝ) ≤ √(17 / (100 * 12578) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12578) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2214838451 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39497195357 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12578) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12578) ≤ (3513609 / 31250000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12578) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12578 * (162 : ℝ) ^ 2 + 26 / (10 * 12578) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12578) : ℝ)) (tA 12578 * 162 ^ 2 + 26 / (10 * 12578)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((735273 / 200000000))) * ((61318867 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((735273 / 200000000)) ^ 3) * ((1560028441 / 1000000000000000000000000))) + ((5529874933 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((735273 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12578) : ℝ)) d.D d.V d.P (√(tA 12578) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((735273 / 200000000)) ^ 2 * (((2214838451 / 1000000000000000)) * ((39497195357 / 1000000000000000000)))) + ((5529874933 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12578) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((735273 / 200000000)) * ((61318867 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12578) : ℝ)) (tA 12578 * 162 ^ 2 + 26 / (10 * 12578)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((61318867 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((735273 / 200000000)) ^ 2) * ((1560028441 / 1000000000000000000000000)) + ((5529874933 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12578) : ℝ)) (√(26 / (10 * 12578) : ℝ)) d.D d.V d.P (√(tA 12578) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((735273 / 200000000)) * (((2214838451 / 1000000000000000)) * ((39497195357 / 1000000000000000000))) + ((5529874933 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12578) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((61318867 / 12500000000000000000) : ℝ) + ((5529874933 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12578

namespace BstLean.Part266.Row12578
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12578 162 ∧
    0 ≤ (tableEnvelope C).f1 12578 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12578 162 ∧
    0 ≤ (tableEnvelope C).w1 12578 162 ∧ 0 ≤ (tableEnvelope C).w2 12578 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12578 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12578 162 ∧ 0 ≤ d.f1 12578 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12578 162 ∧ 0 ≤ d.w1 12578 162 ∧ 0 ≤ d.w2 12578 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12578 ≤ 2 * (228 / 100 : ℝ) / 12578 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12578 ≤ 2 * (370 / 100 : ℝ) / 12578 := by
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
    (completeRAData (tableEnvelope C) 12578 162).locationBound 12578 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12578 162).energyBound 12578 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12578 162) (d.f1 12578 162) d.f2 ≤
      32 * (((58683041 / 12500000000000000) : ℝ) + (783106277 / 500000000000000000) + (94109943 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12578 162) (d.w1 12578 162)
      (d.w2 12578 162) ≤
      32 * (((1887064417 / 100000000000000000000) : ℝ) + (1342610303 / 100000000000000000000) + (490556293 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12578 162) (d.f1 12578 162) d.f2 ≤
      ((58683041 / 12500000000000000) : ℝ) ^ 2 + 2 * ((58683041 / 12500000000000000)) * ((783106277 / 500000000000000000)) * (126 / 100) +
      2 * (((783106277 / 500000000000000000)) ^ 2 + 2 * ((58683041 / 12500000000000000)) * ((94109943 / 250000000000000000))) +
      6 * ((783106277 / 500000000000000000)) * ((94109943 / 250000000000000000)) * (126 / 100) + 8 * ((94109943 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12578 162) (d.f1 12578 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12578 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12578 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12578 162) (d.f1 12578 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12578 162) (d.w1 12578 162) (d.w2 12578 162)
  have hwexpr0 : 0 ≤ d.w0 12578 162 + d.w1 12578 162 * √(π / 2) +
      2 * d.w2 12578 162 + energyR16 12578 *
      radiusPolynomialRoot16 (d.w0 12578 162) (d.w1 12578 162) (d.w2 12578 162) := by
    positivity
  constructor
  · change (12578 : ℝ) ^ 8 * (mA 12578 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12578 162) (d.f1 12578 162) d.f2 + locationR16 12578 *
        radiusPolynomialRoot16 (d.f0 12578 162) (d.f1 12578 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12578 : ℝ) ^ 8 * (mA 12578 : ℝ) ^ 8 *
        ((((58683041 / 12500000000000000) : ℝ) ^ 2 + 2 * ((58683041 / 12500000000000000)) * ((783106277 / 500000000000000000)) * (126 / 100) +
          2 * (((783106277 / 500000000000000000)) ^ 2 + 2 * ((58683041 / 12500000000000000)) * ((94109943 / 250000000000000000))) +
          6 * ((783106277 / 500000000000000000)) * ((94109943 / 250000000000000000)) * (126 / 100) + 8 * ((94109943 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12578) *
          (32 * (((58683041 / 12500000000000000) : ℝ) + (783106277 / 500000000000000000) + (94109943 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12578 : ℝ) ^ 16 *
      (d.w0 12578 162 + d.w1 12578 162 * √(π / 2) + 2 * d.w2 12578 162 +
        energyR16 12578 * radiusPolynomialRoot16 (d.w0 12578 162) (d.w1 12578 162)
          (d.w2 12578 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12578 : ℝ) ^ 16 *
        (((1887064417 / 100000000000000000000) : ℝ) + ((1342610303 / 100000000000000000000)) * (126 / 100) + 2 * ((490556293 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12578) *
          (32 * (((1887064417 / 100000000000000000000) : ℝ) + (1342610303 / 100000000000000000000) + (490556293 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12578

/-! A coarse bound on the actual paper statistics constant at dimension 12579. -/
namespace BstLean.Part266.Row12579
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12577 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12577 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12577 128 ≤ (12831 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12831 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12579) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12579 : ℕ))
    (by norm_num : (12579 : ℕ) ≤ 16384)
  have ht : paperTail256 12579 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12579 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12579 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12579 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12579 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12579 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12577 128 * √(2 / (12579 : ℝ)) *
      (√(12579 : ℝ) + paperT0 12579 + paperTail256 12579) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12579 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12579 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12579 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12577 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12577 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12579 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12579

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12579
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12579 (61 / 100) 162 (17 / (100 * 12579)) (26 / (10 * 12579)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12579 (61 / 100) 162 (17 / (100 * 12579)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (245216973 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (779766203 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (276316227 / 50000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12579 / 12579 * (61 / 100)) ^ 4 * inverseRadius8 (12579 - 1) /
            envelopeGap 12579 (61 / 100) 162 (17 / (100 * 12579)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12579

namespace BstLean.Part266.Row12579
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12579 162 ≤ (4693709749 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12579 162 ≤ (782950581 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (376364943 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12579 162 ≤ (75464571 / 4000000000000000000)
  w1 : (tableEnvelope C).w1 12579 162 ≤ (671145029 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12579 162 ≤ (4904393 / 1000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (245216973 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (245216973 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (779766203 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (276316227 / 50000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3676219 / 1000000000) : ℝ) ≤ √(17 / (100 * 12579) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12579) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (221457433 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39490915487 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12579) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12579) ≤ (2248531 / 20000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12579) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12579 * (162 : ℝ) ^ 2 + 26 / (10 * 12579) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12579) : ℝ)) (tA 12579 * 162 ^ 2 + 26 / (10 * 12579)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3676219 / 1000000000))) * ((245216973 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3676219 / 1000000000)) ^ 3) * ((779766203 / 500000000000000000000000))) + ((276316227 / 50000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3676219 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12579) : ℝ)) d.D d.V d.P (√(tA 12579) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3676219 / 1000000000)) ^ 2 * (((221457433 / 100000000000000)) * ((39490915487 / 1000000000000000000)))) + ((276316227 / 50000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12579) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3676219 / 1000000000)) * ((245216973 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12579) : ℝ)) (tA 12579 * 162 ^ 2 + 26 / (10 * 12579)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((245216973 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3676219 / 1000000000)) ^ 2) * ((779766203 / 500000000000000000000000)) + ((276316227 / 50000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12579) : ℝ)) (√(26 / (10 * 12579) : ℝ)) d.D d.V d.P (√(tA 12579) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3676219 / 1000000000)) * (((221457433 / 100000000000000)) * ((39490915487 / 1000000000000000000))) + ((276316227 / 50000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12579) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((245216973 / 50000000000000000000) : ℝ) + ((276316227 / 50000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12579

namespace BstLean.Part266.Row12579
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12579 162 ∧
    0 ≤ (tableEnvelope C).f1 12579 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12579 162 ∧
    0 ≤ (tableEnvelope C).w1 12579 162 ∧ 0 ≤ (tableEnvelope C).w2 12579 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12579 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12579 162 ∧ 0 ≤ d.f1 12579 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12579 162 ∧ 0 ≤ d.w1 12579 162 ∧ 0 ≤ d.w2 12579 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12579 ≤ 2 * (228 / 100 : ℝ) / 12579 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12579 ≤ 2 * (370 / 100 : ℝ) / 12579 := by
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
    (completeRAData (tableEnvelope C) 12579 162).locationBound 12579 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12579 162).energyBound 12579 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12579 162) (d.f1 12579 162) d.f2 ≤
      32 * (((4693709749 / 1000000000000000000) : ℝ) + (782950581 / 500000000000000000) + (376364943 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12579 162) (d.w1 12579 162)
      (d.w2 12579 162) ≤
      32 * (((75464571 / 4000000000000000000) : ℝ) + (671145029 / 50000000000000000000) + (4904393 / 1000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12579 162) (d.f1 12579 162) d.f2 ≤
      ((4693709749 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4693709749 / 1000000000000000000)) * ((782950581 / 500000000000000000)) * (126 / 100) +
      2 * (((782950581 / 500000000000000000)) ^ 2 + 2 * ((4693709749 / 1000000000000000000)) * ((376364943 / 1000000000000000000))) +
      6 * ((782950581 / 500000000000000000)) * ((376364943 / 1000000000000000000)) * (126 / 100) + 8 * ((376364943 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12579 162) (d.f1 12579 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12579 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12579 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12579 162) (d.f1 12579 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12579 162) (d.w1 12579 162) (d.w2 12579 162)
  have hwexpr0 : 0 ≤ d.w0 12579 162 + d.w1 12579 162 * √(π / 2) +
      2 * d.w2 12579 162 + energyR16 12579 *
      radiusPolynomialRoot16 (d.w0 12579 162) (d.w1 12579 162) (d.w2 12579 162) := by
    positivity
  constructor
  · change (12579 : ℝ) ^ 8 * (mA 12579 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12579 162) (d.f1 12579 162) d.f2 + locationR16 12579 *
        radiusPolynomialRoot16 (d.f0 12579 162) (d.f1 12579 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12579 : ℝ) ^ 8 * (mA 12579 : ℝ) ^ 8 *
        ((((4693709749 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4693709749 / 1000000000000000000)) * ((782950581 / 500000000000000000)) * (126 / 100) +
          2 * (((782950581 / 500000000000000000)) ^ 2 + 2 * ((4693709749 / 1000000000000000000)) * ((376364943 / 1000000000000000000))) +
          6 * ((782950581 / 500000000000000000)) * ((376364943 / 1000000000000000000)) * (126 / 100) + 8 * ((376364943 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12579) *
          (32 * (((4693709749 / 1000000000000000000) : ℝ) + (782950581 / 500000000000000000) + (376364943 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12579 : ℝ) ^ 16 *
      (d.w0 12579 162 + d.w1 12579 162 * √(π / 2) + 2 * d.w2 12579 162 +
        energyR16 12579 * radiusPolynomialRoot16 (d.w0 12579 162) (d.w1 12579 162)
          (d.w2 12579 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12579 : ℝ) ^ 16 *
        (((75464571 / 4000000000000000000) : ℝ) + ((671145029 / 50000000000000000000)) * (126 / 100) + 2 * ((4904393 / 1000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12579) *
          (32 * (((75464571 / 4000000000000000000) : ℝ) + (671145029 / 50000000000000000000) + (4904393 / 1000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12579

/-! A coarse bound on the actual paper statistics constant at dimension 12580. -/
namespace BstLean.Part266.Row12580
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12578 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12578 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12578 128 ≤ (12832 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12832 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12580) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12580 : ℕ))
    (by norm_num : (12580 : ℕ) ≤ 16384)
  have ht : paperTail256 12580 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12580 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12580 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12580 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12580 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12580 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12578 128 * √(2 / (12580 : ℝ)) *
      (√(12580 : ℝ) + paperT0 12580 + paperTail256 12580) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12580 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12580 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12580 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12578 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12578 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12580 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12580

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12580
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12580 (61 / 100) 162 (17 / (100 * 12580)) (26 / (10 * 12580)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12580 (61 / 100) 162 (17 / (100 * 12580)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (245158497 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1559036569 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2761388357 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12580 / 12580 * (61 / 100)) ^ 4 * inverseRadius8 (12580 - 1) /
            envelopeGap 12580 (61 / 100) 162 (17 / (100 * 12580)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12580

namespace BstLean.Part266.Row12580
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12580 162 ≤ (938555309 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12580 162 ≤ (782794937 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (47036267 / 125000000000000000)
  w0 : (tableEnvelope C).w0 12580 162 ≤ (1886164291 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12580 162 ≤ (335492481 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12580 162 ≤ (61290293 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (245158497 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (245158497 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1559036569 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2761388357 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3676073 / 1000000000) : ℝ) ≤ √(17 / (100 * 12580) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12580) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2214310263 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39484637127 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12580) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12580) ≤ (112417613 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12580) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12580 * (162 : ℝ) ^ 2 + 26 / (10 * 12580) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12580) : ℝ)) (tA 12580 * 162 ^ 2 + 26 / (10 * 12580)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3676073 / 1000000000))) * ((245158497 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3676073 / 1000000000)) ^ 3) * ((1559036569 / 1000000000000000000000000))) + ((2761388357 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3676073 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12580) : ℝ)) d.D d.V d.P (√(tA 12580) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3676073 / 1000000000)) ^ 2 * (((2214310263 / 1000000000000000)) * ((39484637127 / 1000000000000000000)))) + ((2761388357 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12580) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3676073 / 1000000000)) * ((245158497 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12580) : ℝ)) (tA 12580 * 162 ^ 2 + 26 / (10 * 12580)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((245158497 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3676073 / 1000000000)) ^ 2) * ((1559036569 / 1000000000000000000000000)) + ((2761388357 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12580) : ℝ)) (√(26 / (10 * 12580) : ℝ)) d.D d.V d.P (√(tA 12580) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3676073 / 1000000000)) * (((2214310263 / 1000000000000000)) * ((39484637127 / 1000000000000000000))) + ((2761388357 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12580) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((245158497 / 50000000000000000000) : ℝ) + ((2761388357 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12580

namespace BstLean.Part266.Row12580
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12580 162 ∧
    0 ≤ (tableEnvelope C).f1 12580 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12580 162 ∧
    0 ≤ (tableEnvelope C).w1 12580 162 ∧ 0 ≤ (tableEnvelope C).w2 12580 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12580 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12580 162 ∧ 0 ≤ d.f1 12580 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12580 162 ∧ 0 ≤ d.w1 12580 162 ∧ 0 ≤ d.w2 12580 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12580 ≤ 2 * (228 / 100 : ℝ) / 12580 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12580 ≤ 2 * (370 / 100 : ℝ) / 12580 := by
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
    (completeRAData (tableEnvelope C) 12580 162).locationBound 12580 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12580 162).energyBound 12580 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12580 162) (d.f1 12580 162) d.f2 ≤
      32 * (((938555309 / 200000000000000000) : ℝ) + (782794937 / 500000000000000000) + (47036267 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12580 162) (d.w1 12580 162)
      (d.w2 12580 162) ≤
      32 * (((1886164291 / 100000000000000000000) : ℝ) + (335492481 / 25000000000000000000) + (61290293 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12580 162) (d.f1 12580 162) d.f2 ≤
      ((938555309 / 200000000000000000) : ℝ) ^ 2 + 2 * ((938555309 / 200000000000000000)) * ((782794937 / 500000000000000000)) * (126 / 100) +
      2 * (((782794937 / 500000000000000000)) ^ 2 + 2 * ((938555309 / 200000000000000000)) * ((47036267 / 125000000000000000))) +
      6 * ((782794937 / 500000000000000000)) * ((47036267 / 125000000000000000)) * (126 / 100) + 8 * ((47036267 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12580 162) (d.f1 12580 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12580 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12580 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12580 162) (d.f1 12580 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12580 162) (d.w1 12580 162) (d.w2 12580 162)
  have hwexpr0 : 0 ≤ d.w0 12580 162 + d.w1 12580 162 * √(π / 2) +
      2 * d.w2 12580 162 + energyR16 12580 *
      radiusPolynomialRoot16 (d.w0 12580 162) (d.w1 12580 162) (d.w2 12580 162) := by
    positivity
  constructor
  · change (12580 : ℝ) ^ 8 * (mA 12580 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12580 162) (d.f1 12580 162) d.f2 + locationR16 12580 *
        radiusPolynomialRoot16 (d.f0 12580 162) (d.f1 12580 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12580 : ℝ) ^ 8 * (mA 12580 : ℝ) ^ 8 *
        ((((938555309 / 200000000000000000) : ℝ) ^ 2 + 2 * ((938555309 / 200000000000000000)) * ((782794937 / 500000000000000000)) * (126 / 100) +
          2 * (((782794937 / 500000000000000000)) ^ 2 + 2 * ((938555309 / 200000000000000000)) * ((47036267 / 125000000000000000))) +
          6 * ((782794937 / 500000000000000000)) * ((47036267 / 125000000000000000)) * (126 / 100) + 8 * ((47036267 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12580) *
          (32 * (((938555309 / 200000000000000000) : ℝ) + (782794937 / 500000000000000000) + (47036267 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12580 : ℝ) ^ 16 *
      (d.w0 12580 162 + d.w1 12580 162 * √(π / 2) + 2 * d.w2 12580 162 +
        energyR16 12580 * radiusPolynomialRoot16 (d.w0 12580 162) (d.w1 12580 162)
          (d.w2 12580 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12580 : ℝ) ^ 16 *
        (((1886164291 / 100000000000000000000) : ℝ) + ((335492481 / 25000000000000000000)) * (126 / 100) + 2 * ((61290293 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12580) *
          (32 * (((1886164291 / 100000000000000000000) : ℝ) + (335492481 / 25000000000000000000) + (61290293 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12580

/-! A coarse bound on the actual paper statistics constant at dimension 12581. -/
namespace BstLean.Part266.Row12581
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12579 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12579 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12579 128 ≤ (12833 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12833 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12581) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12581 : ℕ))
    (by norm_num : (12581 : ℕ) ≤ 16384)
  have ht : paperTail256 12581 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12581 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12581 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12581 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12581 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12581 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12579 128 * √(2 / (12581 : ℝ)) *
      (√(12581 : ℝ) + paperT0 12581 + paperTail256 12581) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12581 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12581 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12581 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12579 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12579 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12581 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12581

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12581
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12581 (61 / 100) 162 (17 / (100 * 12581)) (26 / (10 * 12581)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12581 (61 / 100) 162 (17 / (100 * 12581)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (245100039 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (12176101 / 7812500000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1379807863 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12581 / 12581 * (61 / 100)) ^ 4 * inverseRadius8 (12581 - 1) /
            envelopeGap 12581 (61 / 100) 162 (17 / (100 * 12581)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12581

namespace BstLean.Part266.Row12581
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12581 162 ≤ (234592183 / 50000000000000000)
  f1 : (tableEnvelope C).f1 12581 162 ≤ (313055737 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (47026919 / 125000000000000000)
  w0 : (tableEnvelope C).w0 12581 162 ≤ (1885714461 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12581 162 ≤ (167706237 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 12581 162 ≤ (19608217 / 4000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (245100039 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (245100039 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (12176101 / 7812500000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1379807863 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3675927 / 1000000000) : ℝ) ≤ √(17 / (100 * 12581) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12581) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2214046247 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (157913441 / 4000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12581) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12581) ≤ (112408677 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12581) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12581 * (162 : ℝ) ^ 2 + 26 / (10 * 12581) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12581) : ℝ)) (tA 12581 * 162 ^ 2 + 26 / (10 * 12581)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3675927 / 1000000000))) * ((245100039 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3675927 / 1000000000)) ^ 3) * ((12176101 / 7812500000000000000000))) + ((1379807863 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3675927 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12581) : ℝ)) d.D d.V d.P (√(tA 12581) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3675927 / 1000000000)) ^ 2 * (((2214046247 / 1000000000000000)) * ((157913441 / 4000000000000000)))) + ((1379807863 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12581) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3675927 / 1000000000)) * ((245100039 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12581) : ℝ)) (tA 12581 * 162 ^ 2 + 26 / (10 * 12581)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((245100039 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3675927 / 1000000000)) ^ 2) * ((12176101 / 7812500000000000000000)) + ((1379807863 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12581) : ℝ)) (√(26 / (10 * 12581) : ℝ)) d.D d.V d.P (√(tA 12581) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3675927 / 1000000000)) * (((2214046247 / 1000000000000000)) * ((157913441 / 4000000000000000))) + ((1379807863 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12581) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((245100039 / 50000000000000000000) : ℝ) + ((1379807863 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12581

namespace BstLean.Part266.Row12581
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12581 162 ∧
    0 ≤ (tableEnvelope C).f1 12581 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12581 162 ∧
    0 ≤ (tableEnvelope C).w1 12581 162 ∧ 0 ≤ (tableEnvelope C).w2 12581 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12581 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12581 162 ∧ 0 ≤ d.f1 12581 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12581 162 ∧ 0 ≤ d.w1 12581 162 ∧ 0 ≤ d.w2 12581 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12581 ≤ 2 * (228 / 100 : ℝ) / 12581 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12581 ≤ 2 * (370 / 100 : ℝ) / 12581 := by
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
    (completeRAData (tableEnvelope C) 12581 162).locationBound 12581 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12581 162).energyBound 12581 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12581 162) (d.f1 12581 162) d.f2 ≤
      32 * (((234592183 / 50000000000000000) : ℝ) + (313055737 / 200000000000000000) + (47026919 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12581 162) (d.w1 12581 162)
      (d.w2 12581 162) ≤
      32 * (((1885714461 / 100000000000000000000) : ℝ) + (167706237 / 12500000000000000000) + (19608217 / 4000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12581 162) (d.f1 12581 162) d.f2 ≤
      ((234592183 / 50000000000000000) : ℝ) ^ 2 + 2 * ((234592183 / 50000000000000000)) * ((313055737 / 200000000000000000)) * (126 / 100) +
      2 * (((313055737 / 200000000000000000)) ^ 2 + 2 * ((234592183 / 50000000000000000)) * ((47026919 / 125000000000000000))) +
      6 * ((313055737 / 200000000000000000)) * ((47026919 / 125000000000000000)) * (126 / 100) + 8 * ((47026919 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12581 162) (d.f1 12581 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12581 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12581 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12581 162) (d.f1 12581 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12581 162) (d.w1 12581 162) (d.w2 12581 162)
  have hwexpr0 : 0 ≤ d.w0 12581 162 + d.w1 12581 162 * √(π / 2) +
      2 * d.w2 12581 162 + energyR16 12581 *
      radiusPolynomialRoot16 (d.w0 12581 162) (d.w1 12581 162) (d.w2 12581 162) := by
    positivity
  constructor
  · change (12581 : ℝ) ^ 8 * (mA 12581 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12581 162) (d.f1 12581 162) d.f2 + locationR16 12581 *
        radiusPolynomialRoot16 (d.f0 12581 162) (d.f1 12581 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12581 : ℝ) ^ 8 * (mA 12581 : ℝ) ^ 8 *
        ((((234592183 / 50000000000000000) : ℝ) ^ 2 + 2 * ((234592183 / 50000000000000000)) * ((313055737 / 200000000000000000)) * (126 / 100) +
          2 * (((313055737 / 200000000000000000)) ^ 2 + 2 * ((234592183 / 50000000000000000)) * ((47026919 / 125000000000000000))) +
          6 * ((313055737 / 200000000000000000)) * ((47026919 / 125000000000000000)) * (126 / 100) + 8 * ((47026919 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12581) *
          (32 * (((234592183 / 50000000000000000) : ℝ) + (313055737 / 200000000000000000) + (47026919 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12581 : ℝ) ^ 16 *
      (d.w0 12581 162 + d.w1 12581 162 * √(π / 2) + 2 * d.w2 12581 162 +
        energyR16 12581 * radiusPolynomialRoot16 (d.w0 12581 162) (d.w1 12581 162)
          (d.w2 12581 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12581 : ℝ) ^ 16 *
        (((1885714461 / 100000000000000000000) : ℝ) + ((167706237 / 12500000000000000000)) * (126 / 100) + 2 * ((19608217 / 4000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12581) *
          (32 * (((1885714461 / 100000000000000000000) : ℝ) + (167706237 / 12500000000000000000) + (19608217 / 4000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12581

/-! A coarse bound on the actual paper statistics constant at dimension 12582. -/
namespace BstLean.Part266.Row12582
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12580 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12580 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12580 128 ≤ (12834 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12834 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12582) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12582 : ℕ))
    (by norm_num : (12582 : ℕ) ≤ 16384)
  have ht : paperTail256 12582 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12582 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12582 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12582 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12582 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12582 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12580 128 * √(2 / (12582 : ℝ)) *
      (√(12582 : ℝ) + paperT0 12582 + paperTail256 12582) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12582 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12582 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12582 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12580 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12580 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12582 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12582

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12582
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12582 (61 / 100) 162 (17 / (100 * 12582)) (26 / (10 * 12582)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12582 (61 / 100) 162 (17 / (100 * 12582)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (153151 / 31250000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (311609097 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2757844377 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12582 / 12582 * (61 / 100)) ^ 4 * inverseRadius8 (12582 - 1) /
            envelopeGap 12582 (61 / 100) 162 (17 / (100 * 12582)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12582

namespace BstLean.Part266.Row12582
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12582 162 ≤ (4690914787 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12582 162 ≤ (31299369 / 20000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (376140693 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12582 162 ≤ (471316387 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12582 162 ≤ (1341330341 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12582 162 ≤ (490088543 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (153151 / 31250000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (153151 / 31250000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (311609097 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2757844377 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((183789 / 50000000) : ℝ) ≤ √(17 / (100 * 12582) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12582) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (553445571 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39472084883 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12582) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12582) ≤ (112399743 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12582) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12582 * (162 : ℝ) ^ 2 + 26 / (10 * 12582) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12582) : ℝ)) (tA 12582 * 162 ^ 2 + 26 / (10 * 12582)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((183789 / 50000000))) * ((153151 / 31250000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((183789 / 50000000)) ^ 3) * ((311609097 / 200000000000000000000000))) + ((2757844377 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((183789 / 50000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12582) : ℝ)) d.D d.V d.P (√(tA 12582) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((183789 / 50000000)) ^ 2 * (((553445571 / 250000000000000)) * ((39472084883 / 1000000000000000000)))) + ((2757844377 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12582) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((183789 / 50000000)) * ((153151 / 31250000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12582) : ℝ)) (tA 12582 * 162 ^ 2 + 26 / (10 * 12582)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((153151 / 31250000000000000) : ℝ) + (24198 / 100000) / (2 * ((183789 / 50000000)) ^ 2) * ((311609097 / 200000000000000000000000)) + ((2757844377 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12582) : ℝ)) (√(26 / (10 * 12582) : ℝ)) d.D d.V d.P (√(tA 12582) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((183789 / 50000000)) * (((553445571 / 250000000000000)) * ((39472084883 / 1000000000000000000))) + ((2757844377 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12582) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((153151 / 31250000000000000) : ℝ) + ((2757844377 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12582

namespace BstLean.Part266.Row12582
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12582 162 ∧
    0 ≤ (tableEnvelope C).f1 12582 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12582 162 ∧
    0 ≤ (tableEnvelope C).w1 12582 162 ∧ 0 ≤ (tableEnvelope C).w2 12582 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12582 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12582 162 ∧ 0 ≤ d.f1 12582 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12582 162 ∧ 0 ≤ d.w1 12582 162 ∧ 0 ≤ d.w2 12582 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12582 ≤ 2 * (228 / 100 : ℝ) / 12582 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12582 ≤ 2 * (370 / 100 : ℝ) / 12582 := by
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
    (completeRAData (tableEnvelope C) 12582 162).locationBound 12582 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12582 162).energyBound 12582 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12582 162) (d.f1 12582 162) d.f2 ≤
      32 * (((4690914787 / 1000000000000000000) : ℝ) + (31299369 / 20000000000000000) + (376140693 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12582 162) (d.w1 12582 162)
      (d.w2 12582 162) ≤
      32 * (((471316387 / 25000000000000000000) : ℝ) + (1341330341 / 100000000000000000000) + (490088543 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12582 162) (d.f1 12582 162) d.f2 ≤
      ((4690914787 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4690914787 / 1000000000000000000)) * ((31299369 / 20000000000000000)) * (126 / 100) +
      2 * (((31299369 / 20000000000000000)) ^ 2 + 2 * ((4690914787 / 1000000000000000000)) * ((376140693 / 1000000000000000000))) +
      6 * ((31299369 / 20000000000000000)) * ((376140693 / 1000000000000000000)) * (126 / 100) + 8 * ((376140693 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12582 162) (d.f1 12582 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12582 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12582 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12582 162) (d.f1 12582 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12582 162) (d.w1 12582 162) (d.w2 12582 162)
  have hwexpr0 : 0 ≤ d.w0 12582 162 + d.w1 12582 162 * √(π / 2) +
      2 * d.w2 12582 162 + energyR16 12582 *
      radiusPolynomialRoot16 (d.w0 12582 162) (d.w1 12582 162) (d.w2 12582 162) := by
    positivity
  constructor
  · change (12582 : ℝ) ^ 8 * (mA 12582 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12582 162) (d.f1 12582 162) d.f2 + locationR16 12582 *
        radiusPolynomialRoot16 (d.f0 12582 162) (d.f1 12582 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12582 : ℝ) ^ 8 * (mA 12582 : ℝ) ^ 8 *
        ((((4690914787 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4690914787 / 1000000000000000000)) * ((31299369 / 20000000000000000)) * (126 / 100) +
          2 * (((31299369 / 20000000000000000)) ^ 2 + 2 * ((4690914787 / 1000000000000000000)) * ((376140693 / 1000000000000000000))) +
          6 * ((31299369 / 20000000000000000)) * ((376140693 / 1000000000000000000)) * (126 / 100) + 8 * ((376140693 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12582) *
          (32 * (((4690914787 / 1000000000000000000) : ℝ) + (31299369 / 20000000000000000) + (376140693 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12582 : ℝ) ^ 16 *
      (d.w0 12582 162 + d.w1 12582 162 * √(π / 2) + 2 * d.w2 12582 162 +
        energyR16 12582 * radiusPolynomialRoot16 (d.w0 12582 162) (d.w1 12582 162)
          (d.w2 12582 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12582 : ℝ) ^ 16 *
        (((471316387 / 25000000000000000000) : ℝ) + ((1341330341 / 100000000000000000000)) * (126 / 100) + 2 * ((490088543 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12582) *
          (32 * (((471316387 / 25000000000000000000) : ℝ) + (1341330341 / 100000000000000000000) + (490088543 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12582

/-! A coarse bound on the actual paper statistics constant at dimension 12583. -/
namespace BstLean.Part266.Row12583
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12581 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12581 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12581 128 ≤ (12835 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12835 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12583) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12583 : ℕ))
    (by norm_num : (12583 : ℕ) ≤ 16384)
  have ht : paperTail256 12583 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12583 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12583 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12583 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12583 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12583 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12581 128 * √(2 / (12583 : ℝ)) *
      (√(12583 : ℝ) + paperT0 12583 + paperTail256 12583) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12583 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12583 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12583 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12581 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12581 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12583 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12583

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12583
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12583 (61 / 100) 162 (17 / (100 * 12583)) (26 / (10 * 12583)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12583 (61 / 100) 162 (17 / (100 * 12583)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (489966359 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1557550239 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (689018577 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12583 / 12583 * (61 / 100)) ^ 4 * inverseRadius8 (12583 - 1) /
            envelopeGap 12583 (61 / 100) 162 (17 / (100 * 12583)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12583

namespace BstLean.Part266.Row12583
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12583 162 ≤ (2344991277 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12583 162 ≤ (312931493 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (188032977 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12583 162 ≤ (58900501 / 3125000000000000000)
  w1 : (tableEnvelope C).w1 12583 162 ≤ (1341010531 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12583 162 ≤ (489971699 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (489966359 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (489966359 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1557550239 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (689018577 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1837817 / 500000000) : ℝ) ≤ √(17 / (100 * 12583) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12583) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1106759187 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7893162203 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12583) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12583) ≤ (112390811 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12583) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12583 * (162 : ℝ) ^ 2 + 26 / (10 * 12583) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12583) : ℝ)) (tA 12583 * 162 ^ 2 + 26 / (10 * 12583)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1837817 / 500000000))) * ((489966359 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1837817 / 500000000)) ^ 3) * ((1557550239 / 1000000000000000000000000))) + ((689018577 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1837817 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12583) : ℝ)) d.D d.V d.P (√(tA 12583) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1837817 / 500000000)) ^ 2 * (((1106759187 / 500000000000000)) * ((7893162203 / 200000000000000000)))) + ((689018577 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12583) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1837817 / 500000000)) * ((489966359 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12583) : ℝ)) (tA 12583 * 162 ^ 2 + 26 / (10 * 12583)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((489966359 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1837817 / 500000000)) ^ 2) * ((1557550239 / 1000000000000000000000000)) + ((689018577 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12583) : ℝ)) (√(26 / (10 * 12583) : ℝ)) d.D d.V d.P (√(tA 12583) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1837817 / 500000000)) * (((1106759187 / 500000000000000)) * ((7893162203 / 200000000000000000))) + ((689018577 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12583) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((489966359 / 100000000000000000000) : ℝ) + ((689018577 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12583

namespace BstLean.Part266.Row12583
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12583 162 ∧
    0 ≤ (tableEnvelope C).f1 12583 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12583 162 ∧
    0 ≤ (tableEnvelope C).w1 12583 162 ∧ 0 ≤ (tableEnvelope C).w2 12583 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12583 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12583 162 ∧ 0 ≤ d.f1 12583 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12583 162 ∧ 0 ≤ d.w1 12583 162 ∧ 0 ≤ d.w2 12583 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12583 ≤ 2 * (228 / 100 : ℝ) / 12583 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12583 ≤ 2 * (370 / 100 : ℝ) / 12583 := by
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
    (completeRAData (tableEnvelope C) 12583 162).locationBound 12583 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12583 162).energyBound 12583 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12583 162) (d.f1 12583 162) d.f2 ≤
      32 * (((2344991277 / 500000000000000000) : ℝ) + (312931493 / 200000000000000000) + (188032977 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12583 162) (d.w1 12583 162)
      (d.w2 12583 162) ≤
      32 * (((58900501 / 3125000000000000000) : ℝ) + (1341010531 / 100000000000000000000) + (489971699 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12583 162) (d.f1 12583 162) d.f2 ≤
      ((2344991277 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2344991277 / 500000000000000000)) * ((312931493 / 200000000000000000)) * (126 / 100) +
      2 * (((312931493 / 200000000000000000)) ^ 2 + 2 * ((2344991277 / 500000000000000000)) * ((188032977 / 500000000000000000))) +
      6 * ((312931493 / 200000000000000000)) * ((188032977 / 500000000000000000)) * (126 / 100) + 8 * ((188032977 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12583 162) (d.f1 12583 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12583 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12583 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12583 162) (d.f1 12583 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12583 162) (d.w1 12583 162) (d.w2 12583 162)
  have hwexpr0 : 0 ≤ d.w0 12583 162 + d.w1 12583 162 * √(π / 2) +
      2 * d.w2 12583 162 + energyR16 12583 *
      radiusPolynomialRoot16 (d.w0 12583 162) (d.w1 12583 162) (d.w2 12583 162) := by
    positivity
  constructor
  · change (12583 : ℝ) ^ 8 * (mA 12583 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12583 162) (d.f1 12583 162) d.f2 + locationR16 12583 *
        radiusPolynomialRoot16 (d.f0 12583 162) (d.f1 12583 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12583 : ℝ) ^ 8 * (mA 12583 : ℝ) ^ 8 *
        ((((2344991277 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2344991277 / 500000000000000000)) * ((312931493 / 200000000000000000)) * (126 / 100) +
          2 * (((312931493 / 200000000000000000)) ^ 2 + 2 * ((2344991277 / 500000000000000000)) * ((188032977 / 500000000000000000))) +
          6 * ((312931493 / 200000000000000000)) * ((188032977 / 500000000000000000)) * (126 / 100) + 8 * ((188032977 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12583) *
          (32 * (((2344991277 / 500000000000000000) : ℝ) + (312931493 / 200000000000000000) + (188032977 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12583 : ℝ) ^ 16 *
      (d.w0 12583 162 + d.w1 12583 162 * √(π / 2) + 2 * d.w2 12583 162 +
        energyR16 12583 * radiusPolynomialRoot16 (d.w0 12583 162) (d.w1 12583 162)
          (d.w2 12583 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12583 : ℝ) ^ 16 *
        (((58900501 / 3125000000000000000) : ℝ) + ((1341010531 / 100000000000000000000)) * (126 / 100) + 2 * ((489971699 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12583) *
          (32 * (((58900501 / 3125000000000000000) : ℝ) + (1341010531 / 100000000000000000000) + (489971699 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12583

/-! A coarse bound on the actual paper statistics constant at dimension 12584. -/
namespace BstLean.Part266.Row12584
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12582 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12582 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12582 128 ≤ (12836 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12836 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12584) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12584 : ℕ))
    (by norm_num : (12584 : ℕ) ≤ 16384)
  have ht : paperTail256 12584 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12584 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12584 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12584 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12584 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12584 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12582 128 * √(2 / (12584 : ℝ)) *
      (√(12584 : ℝ) + paperT0 12584 + paperTail256 12584) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12584 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12584 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12584 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12582 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12582 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12584 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12584

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12584
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12584 (61 / 100) 162 (17 / (100 * 12584)) (26 / (10 * 12584)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12584 (61 / 100) 162 (17 / (100 * 12584)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (97969911 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1557055189 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5508611037 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12584 / 12584 * (61 / 100)) ^ 4 * inverseRadius8 (12584 - 1) /
            envelopeGap 12584 (61 / 100) 162 (17 / (100 * 12584)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12584

namespace BstLean.Part266.Row12584
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12584 162 ≤ (4689050641 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12584 162 ≤ (1564346581 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (187995619 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12584 162 ≤ (1884366671 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12584 162 ≤ (1340690827 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12584 162 ≤ (122463723 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (97969911 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (97969911 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1557055189 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5508611037 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((114859 / 31250000) : ℝ) ≤ √(17 / (100 * 12584) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12584) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (553313629 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4932442329 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12584) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12584) ≤ (112381879 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12584) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12584 * (162 : ℝ) ^ 2 + 26 / (10 * 12584) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12584) : ℝ)) (tA 12584 * 162 ^ 2 + 26 / (10 * 12584)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((114859 / 31250000))) * ((97969911 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((114859 / 31250000)) ^ 3) * ((1557055189 / 1000000000000000000000000))) + ((5508611037 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((114859 / 31250000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12584) : ℝ)) d.D d.V d.P (√(tA 12584) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((114859 / 31250000)) ^ 2 * (((553313629 / 250000000000000)) * ((4932442329 / 125000000000000000)))) + ((5508611037 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12584) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((114859 / 31250000)) * ((97969911 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12584) : ℝ)) (tA 12584 * 162 ^ 2 + 26 / (10 * 12584)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((97969911 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((114859 / 31250000)) ^ 2) * ((1557055189 / 1000000000000000000000000)) + ((5508611037 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12584) : ℝ)) (√(26 / (10 * 12584) : ℝ)) d.D d.V d.P (√(tA 12584) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((114859 / 31250000)) * (((553313629 / 250000000000000)) * ((4932442329 / 125000000000000000))) + ((5508611037 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12584) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((97969911 / 20000000000000000000) : ℝ) + ((5508611037 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12584

namespace BstLean.Part266.Row12584
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12584 162 ∧
    0 ≤ (tableEnvelope C).f1 12584 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12584 162 ∧
    0 ≤ (tableEnvelope C).w1 12584 162 ∧ 0 ≤ (tableEnvelope C).w2 12584 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12584 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12584 162 ∧ 0 ≤ d.f1 12584 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12584 162 ∧ 0 ≤ d.w1 12584 162 ∧ 0 ≤ d.w2 12584 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12584 ≤ 2 * (228 / 100 : ℝ) / 12584 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12584 ≤ 2 * (370 / 100 : ℝ) / 12584 := by
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
    (completeRAData (tableEnvelope C) 12584 162).locationBound 12584 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12584 162).energyBound 12584 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12584 162) (d.f1 12584 162) d.f2 ≤
      32 * (((4689050641 / 1000000000000000000) : ℝ) + (1564346581 / 1000000000000000000) + (187995619 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12584 162) (d.w1 12584 162)
      (d.w2 12584 162) ≤
      32 * (((1884366671 / 100000000000000000000) : ℝ) + (1340690827 / 100000000000000000000) + (122463723 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12584 162) (d.f1 12584 162) d.f2 ≤
      ((4689050641 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4689050641 / 1000000000000000000)) * ((1564346581 / 1000000000000000000)) * (126 / 100) +
      2 * (((1564346581 / 1000000000000000000)) ^ 2 + 2 * ((4689050641 / 1000000000000000000)) * ((187995619 / 500000000000000000))) +
      6 * ((1564346581 / 1000000000000000000)) * ((187995619 / 500000000000000000)) * (126 / 100) + 8 * ((187995619 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12584 162) (d.f1 12584 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12584 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12584 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12584 162) (d.f1 12584 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12584 162) (d.w1 12584 162) (d.w2 12584 162)
  have hwexpr0 : 0 ≤ d.w0 12584 162 + d.w1 12584 162 * √(π / 2) +
      2 * d.w2 12584 162 + energyR16 12584 *
      radiusPolynomialRoot16 (d.w0 12584 162) (d.w1 12584 162) (d.w2 12584 162) := by
    positivity
  constructor
  · change (12584 : ℝ) ^ 8 * (mA 12584 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12584 162) (d.f1 12584 162) d.f2 + locationR16 12584 *
        radiusPolynomialRoot16 (d.f0 12584 162) (d.f1 12584 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12584 : ℝ) ^ 8 * (mA 12584 : ℝ) ^ 8 *
        ((((4689050641 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4689050641 / 1000000000000000000)) * ((1564346581 / 1000000000000000000)) * (126 / 100) +
          2 * (((1564346581 / 1000000000000000000)) ^ 2 + 2 * ((4689050641 / 1000000000000000000)) * ((187995619 / 500000000000000000))) +
          6 * ((1564346581 / 1000000000000000000)) * ((187995619 / 500000000000000000)) * (126 / 100) + 8 * ((187995619 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12584) *
          (32 * (((4689050641 / 1000000000000000000) : ℝ) + (1564346581 / 1000000000000000000) + (187995619 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12584 : ℝ) ^ 16 *
      (d.w0 12584 162 + d.w1 12584 162 * √(π / 2) + 2 * d.w2 12584 162 +
        energyR16 12584 * radiusPolynomialRoot16 (d.w0 12584 162) (d.w1 12584 162)
          (d.w2 12584 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12584 : ℝ) ^ 16 *
        (((1884366671 / 100000000000000000000) : ℝ) + ((1340690827 / 100000000000000000000)) * (126 / 100) + 2 * ((122463723 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12584) *
          (32 * (((1884366671 / 100000000000000000000) : ℝ) + (1340690827 / 100000000000000000000) + (122463723 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12584

/-! A coarse bound on the actual paper statistics constant at dimension 12585. -/
namespace BstLean.Part266.Row12585
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12583 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12583 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12583 128 ≤ (12837 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12837 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12585) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12585 : ℕ))
    (by norm_num : (12585 : ℕ) ≤ 16384)
  have ht : paperTail256 12585 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12585 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12585 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12585 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12585 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12585 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12583 128 * √(2 / (12585 : ℝ)) *
      (√(12585 : ℝ) + paperT0 12585 + paperTail256 12585) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12585 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12585 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12585 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12583 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12583 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12585 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12585

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12585
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12585 (61 / 100) 162 (17 / (100 * 12585)) (26 / (10 * 12585)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12585 (61 / 100) 162 (17 / (100 * 12585)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (122433197 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (97285021 / 62500000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2752538007 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12585 / 12585 * (61 / 100)) ^ 4 * inverseRadius8 (12585 - 1) /
            envelopeGap 12585 (61 / 100) 162 (17 / (100 * 12585)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12585

namespace BstLean.Part266.Row12585
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12585 162 ≤ (4688119053 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12585 162 ≤ (782017899 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (183553 / 488281250000000)
  w0 : (tableEnvelope C).w0 12585 162 ≤ (941958733 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12585 162 ≤ (41886601 / 3125000000000000000)
  w2 : (tableEnvelope C).w2 12585 162 ≤ (489738121 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (122433197 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (122433197 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (97285021 / 62500000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2752538007 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1837671 / 500000000) : ℝ) ≤ √(17 / (100 * 12585) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12585) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (221299071 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39453267749 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12585) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12585) ≤ (112372949 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12585) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12585 * (162 : ℝ) ^ 2 + 26 / (10 * 12585) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12585) : ℝ)) (tA 12585 * 162 ^ 2 + 26 / (10 * 12585)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1837671 / 500000000))) * ((122433197 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1837671 / 500000000)) ^ 3) * ((97285021 / 62500000000000000000000))) + ((2752538007 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1837671 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12585) : ℝ)) d.D d.V d.P (√(tA 12585) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1837671 / 500000000)) ^ 2 * (((221299071 / 100000000000000)) * ((39453267749 / 1000000000000000000)))) + ((2752538007 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12585) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1837671 / 500000000)) * ((122433197 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12585) : ℝ)) (tA 12585 * 162 ^ 2 + 26 / (10 * 12585)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((122433197 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1837671 / 500000000)) ^ 2) * ((97285021 / 62500000000000000000000)) + ((2752538007 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12585) : ℝ)) (√(26 / (10 * 12585) : ℝ)) d.D d.V d.P (√(tA 12585) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1837671 / 500000000)) * (((221299071 / 100000000000000)) * ((39453267749 / 1000000000000000000))) + ((2752538007 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12585) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((122433197 / 25000000000000000000) : ℝ) + ((2752538007 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12585

namespace BstLean.Part266.Row12585
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12585 162 ∧
    0 ≤ (tableEnvelope C).f1 12585 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12585 162 ∧
    0 ≤ (tableEnvelope C).w1 12585 162 ∧ 0 ≤ (tableEnvelope C).w2 12585 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12585 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12585 162 ∧ 0 ≤ d.f1 12585 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12585 162 ∧ 0 ≤ d.w1 12585 162 ∧ 0 ≤ d.w2 12585 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12585 ≤ 2 * (228 / 100 : ℝ) / 12585 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12585 ≤ 2 * (370 / 100 : ℝ) / 12585 := by
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
    (completeRAData (tableEnvelope C) 12585 162).locationBound 12585 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12585 162).energyBound 12585 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12585 162) (d.f1 12585 162) d.f2 ≤
      32 * (((4688119053 / 1000000000000000000) : ℝ) + (782017899 / 500000000000000000) + (183553 / 488281250000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12585 162) (d.w1 12585 162)
      (d.w2 12585 162) ≤
      32 * (((941958733 / 50000000000000000000) : ℝ) + (41886601 / 3125000000000000000) + (489738121 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12585 162) (d.f1 12585 162) d.f2 ≤
      ((4688119053 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4688119053 / 1000000000000000000)) * ((782017899 / 500000000000000000)) * (126 / 100) +
      2 * (((782017899 / 500000000000000000)) ^ 2 + 2 * ((4688119053 / 1000000000000000000)) * ((183553 / 488281250000000))) +
      6 * ((782017899 / 500000000000000000)) * ((183553 / 488281250000000)) * (126 / 100) + 8 * ((183553 / 488281250000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12585 162) (d.f1 12585 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12585 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12585 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12585 162) (d.f1 12585 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12585 162) (d.w1 12585 162) (d.w2 12585 162)
  have hwexpr0 : 0 ≤ d.w0 12585 162 + d.w1 12585 162 * √(π / 2) +
      2 * d.w2 12585 162 + energyR16 12585 *
      radiusPolynomialRoot16 (d.w0 12585 162) (d.w1 12585 162) (d.w2 12585 162) := by
    positivity
  constructor
  · change (12585 : ℝ) ^ 8 * (mA 12585 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12585 162) (d.f1 12585 162) d.f2 + locationR16 12585 *
        radiusPolynomialRoot16 (d.f0 12585 162) (d.f1 12585 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12585 : ℝ) ^ 8 * (mA 12585 : ℝ) ^ 8 *
        ((((4688119053 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4688119053 / 1000000000000000000)) * ((782017899 / 500000000000000000)) * (126 / 100) +
          2 * (((782017899 / 500000000000000000)) ^ 2 + 2 * ((4688119053 / 1000000000000000000)) * ((183553 / 488281250000000))) +
          6 * ((782017899 / 500000000000000000)) * ((183553 / 488281250000000)) * (126 / 100) + 8 * ((183553 / 488281250000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12585) *
          (32 * (((4688119053 / 1000000000000000000) : ℝ) + (782017899 / 500000000000000000) + (183553 / 488281250000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12585 : ℝ) ^ 16 *
      (d.w0 12585 162 + d.w1 12585 162 * √(π / 2) + 2 * d.w2 12585 162 +
        energyR16 12585 * radiusPolynomialRoot16 (d.w0 12585 162) (d.w1 12585 162)
          (d.w2 12585 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12585 : ℝ) ^ 16 *
        (((941958733 / 50000000000000000000) : ℝ) + ((41886601 / 3125000000000000000)) * (126 / 100) + 2 * ((489738121 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12585) *
          (32 * (((941958733 / 50000000000000000000) : ℝ) + (41886601 / 3125000000000000000) + (489738121 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12585

/-! A coarse bound on the actual paper statistics constant at dimension 12586. -/
namespace BstLean.Part266.Row12586
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12584 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12584 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12584 128 ≤ (12838 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12838 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12586) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12586 : ℕ))
    (by norm_num : (12586 : ℕ) ≤ 16384)
  have ht : paperTail256 12586 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12586 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12586 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12586 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12586 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12586 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12584 128 * √(2 / (12586 : ℝ)) *
      (√(12586 : ℝ) + paperT0 12586 + paperTail256 12586) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12586 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12586 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12586 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12584 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12584 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12586 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12586

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12586
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12586 (61 / 100) 162 (17 / (100 * 12586)) (26 / (10 * 12586)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12586 (61 / 100) 162 (17 / (100 * 12586)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (489616059 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1556065679 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2750771773 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12586 / 12586 * (61 / 100)) ^ 4 * inverseRadius8 (12586 - 1) /
            envelopeGap 12586 (61 / 100) 162 (17 / (100 * 12586)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12586

namespace BstLean.Part266.Row12586
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12586 162 ≤ (2343593893 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12586 162 ≤ (1563725117 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (187920937 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12586 162 ≤ (941734209 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12586 162 ≤ (268010349 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12586 162 ≤ (489621389 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (489616059 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (489616059 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1556065679 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2750771773 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((918799 / 250000000) : ℝ) ≤ √(17 / (100 * 12586) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12586) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1106363479 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39446998353 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12586) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12586) ≤ (112364021 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12586) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12586 * (162 : ℝ) ^ 2 + 26 / (10 * 12586) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12586) : ℝ)) (tA 12586 * 162 ^ 2 + 26 / (10 * 12586)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((918799 / 250000000))) * ((489616059 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((918799 / 250000000)) ^ 3) * ((1556065679 / 1000000000000000000000000))) + ((2750771773 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((918799 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12586) : ℝ)) d.D d.V d.P (√(tA 12586) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((918799 / 250000000)) ^ 2 * (((1106363479 / 500000000000000)) * ((39446998353 / 1000000000000000000)))) + ((2750771773 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12586) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((918799 / 250000000)) * ((489616059 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12586) : ℝ)) (tA 12586 * 162 ^ 2 + 26 / (10 * 12586)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((489616059 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((918799 / 250000000)) ^ 2) * ((1556065679 / 1000000000000000000000000)) + ((2750771773 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12586) : ℝ)) (√(26 / (10 * 12586) : ℝ)) d.D d.V d.P (√(tA 12586) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((918799 / 250000000)) * (((1106363479 / 500000000000000)) * ((39446998353 / 1000000000000000000))) + ((2750771773 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12586) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((489616059 / 100000000000000000000) : ℝ) + ((2750771773 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12586

namespace BstLean.Part266.Row12586
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12586 162 ∧
    0 ≤ (tableEnvelope C).f1 12586 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12586 162 ∧
    0 ≤ (tableEnvelope C).w1 12586 162 ∧ 0 ≤ (tableEnvelope C).w2 12586 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12586 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12586 162 ∧ 0 ≤ d.f1 12586 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12586 162 ∧ 0 ≤ d.w1 12586 162 ∧ 0 ≤ d.w2 12586 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12586 ≤ 2 * (228 / 100 : ℝ) / 12586 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12586 ≤ 2 * (370 / 100 : ℝ) / 12586 := by
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
    (completeRAData (tableEnvelope C) 12586 162).locationBound 12586 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12586 162).energyBound 12586 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12586 162) (d.f1 12586 162) d.f2 ≤
      32 * (((2343593893 / 500000000000000000) : ℝ) + (1563725117 / 1000000000000000000) + (187920937 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12586 162) (d.w1 12586 162)
      (d.w2 12586 162) ≤
      32 * (((941734209 / 50000000000000000000) : ℝ) + (268010349 / 20000000000000000000) + (489621389 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12586 162) (d.f1 12586 162) d.f2 ≤
      ((2343593893 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2343593893 / 500000000000000000)) * ((1563725117 / 1000000000000000000)) * (126 / 100) +
      2 * (((1563725117 / 1000000000000000000)) ^ 2 + 2 * ((2343593893 / 500000000000000000)) * ((187920937 / 500000000000000000))) +
      6 * ((1563725117 / 1000000000000000000)) * ((187920937 / 500000000000000000)) * (126 / 100) + 8 * ((187920937 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12586 162) (d.f1 12586 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12586 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12586 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12586 162) (d.f1 12586 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12586 162) (d.w1 12586 162) (d.w2 12586 162)
  have hwexpr0 : 0 ≤ d.w0 12586 162 + d.w1 12586 162 * √(π / 2) +
      2 * d.w2 12586 162 + energyR16 12586 *
      radiusPolynomialRoot16 (d.w0 12586 162) (d.w1 12586 162) (d.w2 12586 162) := by
    positivity
  constructor
  · change (12586 : ℝ) ^ 8 * (mA 12586 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12586 162) (d.f1 12586 162) d.f2 + locationR16 12586 *
        radiusPolynomialRoot16 (d.f0 12586 162) (d.f1 12586 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12586 : ℝ) ^ 8 * (mA 12586 : ℝ) ^ 8 *
        ((((2343593893 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2343593893 / 500000000000000000)) * ((1563725117 / 1000000000000000000)) * (126 / 100) +
          2 * (((1563725117 / 1000000000000000000)) ^ 2 + 2 * ((2343593893 / 500000000000000000)) * ((187920937 / 500000000000000000))) +
          6 * ((1563725117 / 1000000000000000000)) * ((187920937 / 500000000000000000)) * (126 / 100) + 8 * ((187920937 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12586) *
          (32 * (((2343593893 / 500000000000000000) : ℝ) + (1563725117 / 1000000000000000000) + (187920937 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12586 : ℝ) ^ 16 *
      (d.w0 12586 162 + d.w1 12586 162 * √(π / 2) + 2 * d.w2 12586 162 +
        energyR16 12586 * radiusPolynomialRoot16 (d.w0 12586 162) (d.w1 12586 162)
          (d.w2 12586 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12586 : ℝ) ^ 16 *
        (((941734209 / 50000000000000000000) : ℝ) + ((268010349 / 20000000000000000000)) * (126 / 100) + 2 * ((489621389 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12586) *
          (32 * (((941734209 / 50000000000000000000) : ℝ) + (268010349 / 20000000000000000000) + (489621389 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12586

/-! A coarse bound on the actual paper statistics constant at dimension 12587. -/
namespace BstLean.Part266.Row12587
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12585 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12585 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12585 128 ≤ (12839 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12839 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12587) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12587 : ℕ))
    (by norm_num : (12587 : ℕ) ≤ 16384)
  have ht : paperTail256 12587 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12587 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12587 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12587 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12587 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12587 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12585 128 * √(2 / (12587 : ℝ)) *
      (√(12587 : ℝ) + paperT0 12587 + paperTail256 12587) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12587 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12587 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12587 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12585 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12585 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12587 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12587

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12587
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12587 (61 / 100) 162 (17 / (100 * 12587)) (26 / (10 * 12587)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12587 (61 / 100) 162 (17 / (100 * 12587)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (244749683 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1555571219 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5498013631 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12587 / 12587 * (61 / 100)) ^ 4 * inverseRadius8 (12587 - 1) /
            envelopeGap 12587 (61 / 100) 162 (17 / (100 * 12587)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12587

namespace BstLean.Part266.Row12587
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12587 162 ≤ (1171564211 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12587 162 ≤ (195426817 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (15030689 / 40000000000000000)
  w0 : (tableEnvelope C).w0 12587 162 ≤ (75320781 / 4000000000000000000)
  w1 : (tableEnvelope C).w1 12587 162 ≤ (267946473 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12587 162 ≤ (122376173 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (244749683 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (244749683 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1555571219 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5498013631 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((73501 / 20000000) : ℝ) ≤ √(17 / (100 * 12587) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12587) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2212463257 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19720365229 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12587) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12587) ≤ (56177547 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12587) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12587 * (162 : ℝ) ^ 2 + 26 / (10 * 12587) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12587) : ℝ)) (tA 12587 * 162 ^ 2 + 26 / (10 * 12587)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((73501 / 20000000))) * ((244749683 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((73501 / 20000000)) ^ 3) * ((1555571219 / 1000000000000000000000000))) + ((5498013631 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((73501 / 20000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12587) : ℝ)) d.D d.V d.P (√(tA 12587) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((73501 / 20000000)) ^ 2 * (((2212463257 / 1000000000000000)) * ((19720365229 / 500000000000000000)))) + ((5498013631 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12587) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((73501 / 20000000)) * ((244749683 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12587) : ℝ)) (tA 12587 * 162 ^ 2 + 26 / (10 * 12587)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((244749683 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((73501 / 20000000)) ^ 2) * ((1555571219 / 1000000000000000000000000)) + ((5498013631 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12587) : ℝ)) (√(26 / (10 * 12587) : ℝ)) d.D d.V d.P (√(tA 12587) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((73501 / 20000000)) * (((2212463257 / 1000000000000000)) * ((19720365229 / 500000000000000000))) + ((5498013631 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12587) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((244749683 / 50000000000000000000) : ℝ) + ((5498013631 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12587

namespace BstLean.Part266.Row12587
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12587 162 ∧
    0 ≤ (tableEnvelope C).f1 12587 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12587 162 ∧
    0 ≤ (tableEnvelope C).w1 12587 162 ∧ 0 ≤ (tableEnvelope C).w2 12587 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12587 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12587 162 ∧ 0 ≤ d.f1 12587 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12587 162 ∧ 0 ≤ d.w1 12587 162 ∧ 0 ≤ d.w2 12587 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12587 ≤ 2 * (228 / 100 : ℝ) / 12587 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12587 ≤ 2 * (370 / 100 : ℝ) / 12587 := by
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
    (completeRAData (tableEnvelope C) 12587 162).locationBound 12587 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12587 162).energyBound 12587 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12587 162) (d.f1 12587 162) d.f2 ≤
      32 * (((1171564211 / 250000000000000000) : ℝ) + (195426817 / 125000000000000000) + (15030689 / 40000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12587 162) (d.w1 12587 162)
      (d.w2 12587 162) ≤
      32 * (((75320781 / 4000000000000000000) : ℝ) + (267946473 / 20000000000000000000) + (122376173 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12587 162) (d.f1 12587 162) d.f2 ≤
      ((1171564211 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1171564211 / 250000000000000000)) * ((195426817 / 125000000000000000)) * (126 / 100) +
      2 * (((195426817 / 125000000000000000)) ^ 2 + 2 * ((1171564211 / 250000000000000000)) * ((15030689 / 40000000000000000))) +
      6 * ((195426817 / 125000000000000000)) * ((15030689 / 40000000000000000)) * (126 / 100) + 8 * ((15030689 / 40000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12587 162) (d.f1 12587 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12587 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12587 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12587 162) (d.f1 12587 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12587 162) (d.w1 12587 162) (d.w2 12587 162)
  have hwexpr0 : 0 ≤ d.w0 12587 162 + d.w1 12587 162 * √(π / 2) +
      2 * d.w2 12587 162 + energyR16 12587 *
      radiusPolynomialRoot16 (d.w0 12587 162) (d.w1 12587 162) (d.w2 12587 162) := by
    positivity
  constructor
  · change (12587 : ℝ) ^ 8 * (mA 12587 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12587 162) (d.f1 12587 162) d.f2 + locationR16 12587 *
        radiusPolynomialRoot16 (d.f0 12587 162) (d.f1 12587 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12587 : ℝ) ^ 8 * (mA 12587 : ℝ) ^ 8 *
        ((((1171564211 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1171564211 / 250000000000000000)) * ((195426817 / 125000000000000000)) * (126 / 100) +
          2 * (((195426817 / 125000000000000000)) ^ 2 + 2 * ((1171564211 / 250000000000000000)) * ((15030689 / 40000000000000000))) +
          6 * ((195426817 / 125000000000000000)) * ((15030689 / 40000000000000000)) * (126 / 100) + 8 * ((15030689 / 40000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12587) *
          (32 * (((1171564211 / 250000000000000000) : ℝ) + (195426817 / 125000000000000000) + (15030689 / 40000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12587 : ℝ) ^ 16 *
      (d.w0 12587 162 + d.w1 12587 162 * √(π / 2) + 2 * d.w2 12587 162 +
        energyR16 12587 * radiusPolynomialRoot16 (d.w0 12587 162) (d.w1 12587 162)
          (d.w2 12587 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12587 : ℝ) ^ 16 *
        (((75320781 / 4000000000000000000) : ℝ) + ((267946473 / 20000000000000000000)) * (126 / 100) + 2 * ((122376173 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12587) *
          (32 * (((75320781 / 4000000000000000000) : ℝ) + (267946473 / 20000000000000000000) + (122376173 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12587

/-! A coarse bound on the actual paper statistics constant at dimension 12588. -/
namespace BstLean.Part266.Row12588
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12586 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12586 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12586 128 ≤ (12840 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12840 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12588) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12588 : ℕ))
    (by norm_num : (12588 : ℕ) ≤ 16384)
  have ht : paperTail256 12588 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12588 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12588 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12588 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12588 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12588 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12586 128 * √(2 / (12588 : ℝ)) *
      (√(12588 : ℝ) + paperT0 12588 + paperTail256 12588) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12588 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12588 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12588 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12586 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12586 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12588 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12588

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12588
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12588 (61 / 100) 162 (17 / (100 * 12588)) (26 / (10 * 12588)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12588 (61 / 100) 162 (17 / (100 * 12588)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (489382711 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (388769239 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2747243133 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12588 / 12588 * (61 / 100)) ^ 4 * inverseRadius8 (12588 - 1) /
            envelopeGap 12588 (61 / 100) 162 (17 / (100 * 12588)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12588

namespace BstLean.Part266.Row12588
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12588 162 ≤ (4685326227 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12588 162 ≤ (1563104057 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (375692599 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12588 162 ≤ (1882570789 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12588 162 ≤ (669706547 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12588 162 ≤ (244694017 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (489382711 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (489382711 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (388769239 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2747243133 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((459363 / 125000000) : ℝ) ≤ √(17 / (100 * 12588) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12588) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2212199609 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (616163501 / 15625000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12588) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12588) ≤ (14043271 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12588) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12588 * (162 : ℝ) ^ 2 + 26 / (10 * 12588) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12588) : ℝ)) (tA 12588 * 162 ^ 2 + 26 / (10 * 12588)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((459363 / 125000000))) * ((489382711 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((459363 / 125000000)) ^ 3) * ((388769239 / 250000000000000000000000))) + ((2747243133 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((459363 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12588) : ℝ)) d.D d.V d.P (√(tA 12588) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((459363 / 125000000)) ^ 2 * (((2212199609 / 1000000000000000)) * ((616163501 / 15625000000000000)))) + ((2747243133 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12588) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((459363 / 125000000)) * ((489382711 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12588) : ℝ)) (tA 12588 * 162 ^ 2 + 26 / (10 * 12588)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((489382711 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((459363 / 125000000)) ^ 2) * ((388769239 / 250000000000000000000000)) + ((2747243133 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12588) : ℝ)) (√(26 / (10 * 12588) : ℝ)) d.D d.V d.P (√(tA 12588) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((459363 / 125000000)) * (((2212199609 / 1000000000000000)) * ((616163501 / 15625000000000000))) + ((2747243133 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12588) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((489382711 / 100000000000000000000) : ℝ) + ((2747243133 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12588

namespace BstLean.Part266.Row12588
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12588 162 ∧
    0 ≤ (tableEnvelope C).f1 12588 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12588 162 ∧
    0 ≤ (tableEnvelope C).w1 12588 162 ∧ 0 ≤ (tableEnvelope C).w2 12588 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12588 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12588 162 ∧ 0 ≤ d.f1 12588 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12588 162 ∧ 0 ≤ d.w1 12588 162 ∧ 0 ≤ d.w2 12588 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12588 ≤ 2 * (228 / 100 : ℝ) / 12588 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12588 ≤ 2 * (370 / 100 : ℝ) / 12588 := by
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
    (completeRAData (tableEnvelope C) 12588 162).locationBound 12588 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12588 162).energyBound 12588 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12588 162) (d.f1 12588 162) d.f2 ≤
      32 * (((4685326227 / 1000000000000000000) : ℝ) + (1563104057 / 1000000000000000000) + (375692599 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12588 162) (d.w1 12588 162)
      (d.w2 12588 162) ≤
      32 * (((1882570789 / 100000000000000000000) : ℝ) + (669706547 / 50000000000000000000) + (244694017 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12588 162) (d.f1 12588 162) d.f2 ≤
      ((4685326227 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4685326227 / 1000000000000000000)) * ((1563104057 / 1000000000000000000)) * (126 / 100) +
      2 * (((1563104057 / 1000000000000000000)) ^ 2 + 2 * ((4685326227 / 1000000000000000000)) * ((375692599 / 1000000000000000000))) +
      6 * ((1563104057 / 1000000000000000000)) * ((375692599 / 1000000000000000000)) * (126 / 100) + 8 * ((375692599 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12588 162) (d.f1 12588 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12588 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12588 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12588 162) (d.f1 12588 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12588 162) (d.w1 12588 162) (d.w2 12588 162)
  have hwexpr0 : 0 ≤ d.w0 12588 162 + d.w1 12588 162 * √(π / 2) +
      2 * d.w2 12588 162 + energyR16 12588 *
      radiusPolynomialRoot16 (d.w0 12588 162) (d.w1 12588 162) (d.w2 12588 162) := by
    positivity
  constructor
  · change (12588 : ℝ) ^ 8 * (mA 12588 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12588 162) (d.f1 12588 162) d.f2 + locationR16 12588 *
        radiusPolynomialRoot16 (d.f0 12588 162) (d.f1 12588 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12588 : ℝ) ^ 8 * (mA 12588 : ℝ) ^ 8 *
        ((((4685326227 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4685326227 / 1000000000000000000)) * ((1563104057 / 1000000000000000000)) * (126 / 100) +
          2 * (((1563104057 / 1000000000000000000)) ^ 2 + 2 * ((4685326227 / 1000000000000000000)) * ((375692599 / 1000000000000000000))) +
          6 * ((1563104057 / 1000000000000000000)) * ((375692599 / 1000000000000000000)) * (126 / 100) + 8 * ((375692599 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12588) *
          (32 * (((4685326227 / 1000000000000000000) : ℝ) + (1563104057 / 1000000000000000000) + (375692599 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12588 : ℝ) ^ 16 *
      (d.w0 12588 162 + d.w1 12588 162 * √(π / 2) + 2 * d.w2 12588 162 +
        energyR16 12588 * radiusPolynomialRoot16 (d.w0 12588 162) (d.w1 12588 162)
          (d.w2 12588 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12588 : ℝ) ^ 16 *
        (((1882570789 / 100000000000000000000) : ℝ) + ((669706547 / 50000000000000000000)) * (126 / 100) + 2 * ((244694017 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12588) *
          (32 * (((1882570789 / 100000000000000000000) : ℝ) + (669706547 / 50000000000000000000) + (244694017 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12588

/-! A coarse bound on the actual paper statistics constant at dimension 12589. -/
namespace BstLean.Part266.Row12589
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12587 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12587 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12587 128 ≤ (12841 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12841 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12589) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12589 : ℕ))
    (by norm_num : (12589 : ℕ) ≤ 16384)
  have ht : paperTail256 12589 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12589 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12589 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12589 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12589 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12589 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12587 128 * √(2 / (12589 : ℝ)) *
      (√(12589 : ℝ) + paperT0 12589 + paperTail256 12589) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12589 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12589 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12589 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12587 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12587 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12589 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12589

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12589
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12589 (61 / 100) 162 (17 / (100 * 12589)) (26 / (10 * 12589)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12589 (61 / 100) 162 (17 / (100 * 12589)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (122316523 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (194322861 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5490961449 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12589 / 12589 * (61 / 100)) ^ 4 * inverseRadius8 (12589 - 1) /
            envelopeGap 12589 (61 / 100) 162 (17 / (100 * 12589)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12589

namespace BstLean.Part266.Row12589
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12589 162 ≤ (585549491 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12589 162 ≤ (781396839 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (75123599 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12589 162 ≤ (1882122207 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12589 162 ≤ (133909393 / 10000000000000000000)
  w2 : (tableEnvelope C).w2 12589 162 ≤ (122317853 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (122316523 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (122316523 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (194322861 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5490961449 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1837379 / 500000000) : ℝ) ≤ √(17 / (100 * 12589) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12589) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (552984003 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9857049787 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12589) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12589) ≤ (28084311 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12589) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12589 * (162 : ℝ) ^ 2 + 26 / (10 * 12589) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12589) : ℝ)) (tA 12589 * 162 ^ 2 + 26 / (10 * 12589)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1837379 / 500000000))) * ((122316523 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1837379 / 500000000)) ^ 3) * ((194322861 / 125000000000000000000000))) + ((5490961449 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1837379 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12589) : ℝ)) d.D d.V d.P (√(tA 12589) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1837379 / 500000000)) ^ 2 * (((552984003 / 250000000000000)) * ((9857049787 / 250000000000000000)))) + ((5490961449 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12589) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1837379 / 500000000)) * ((122316523 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12589) : ℝ)) (tA 12589 * 162 ^ 2 + 26 / (10 * 12589)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((122316523 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1837379 / 500000000)) ^ 2) * ((194322861 / 125000000000000000000000)) + ((5490961449 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12589) : ℝ)) (√(26 / (10 * 12589) : ℝ)) d.D d.V d.P (√(tA 12589) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1837379 / 500000000)) * (((552984003 / 250000000000000)) * ((9857049787 / 250000000000000000))) + ((5490961449 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12589) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((122316523 / 25000000000000000000) : ℝ) + ((5490961449 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12589

namespace BstLean.Part266.Row12589
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12589 162 ∧
    0 ≤ (tableEnvelope C).f1 12589 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12589 162 ∧
    0 ≤ (tableEnvelope C).w1 12589 162 ∧ 0 ≤ (tableEnvelope C).w2 12589 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12589 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12589 162 ∧ 0 ≤ d.f1 12589 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12589 162 ∧ 0 ≤ d.w1 12589 162 ∧ 0 ≤ d.w2 12589 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12589 ≤ 2 * (228 / 100 : ℝ) / 12589 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12589 ≤ 2 * (370 / 100 : ℝ) / 12589 := by
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
    (completeRAData (tableEnvelope C) 12589 162).locationBound 12589 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12589 162).energyBound 12589 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12589 162) (d.f1 12589 162) d.f2 ≤
      32 * (((585549491 / 125000000000000000) : ℝ) + (781396839 / 500000000000000000) + (75123599 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12589 162) (d.w1 12589 162)
      (d.w2 12589 162) ≤
      32 * (((1882122207 / 100000000000000000000) : ℝ) + (133909393 / 10000000000000000000) + (122317853 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12589 162) (d.f1 12589 162) d.f2 ≤
      ((585549491 / 125000000000000000) : ℝ) ^ 2 + 2 * ((585549491 / 125000000000000000)) * ((781396839 / 500000000000000000)) * (126 / 100) +
      2 * (((781396839 / 500000000000000000)) ^ 2 + 2 * ((585549491 / 125000000000000000)) * ((75123599 / 200000000000000000))) +
      6 * ((781396839 / 500000000000000000)) * ((75123599 / 200000000000000000)) * (126 / 100) + 8 * ((75123599 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12589 162) (d.f1 12589 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12589 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12589 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12589 162) (d.f1 12589 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12589 162) (d.w1 12589 162) (d.w2 12589 162)
  have hwexpr0 : 0 ≤ d.w0 12589 162 + d.w1 12589 162 * √(π / 2) +
      2 * d.w2 12589 162 + energyR16 12589 *
      radiusPolynomialRoot16 (d.w0 12589 162) (d.w1 12589 162) (d.w2 12589 162) := by
    positivity
  constructor
  · change (12589 : ℝ) ^ 8 * (mA 12589 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12589 162) (d.f1 12589 162) d.f2 + locationR16 12589 *
        radiusPolynomialRoot16 (d.f0 12589 162) (d.f1 12589 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12589 : ℝ) ^ 8 * (mA 12589 : ℝ) ^ 8 *
        ((((585549491 / 125000000000000000) : ℝ) ^ 2 + 2 * ((585549491 / 125000000000000000)) * ((781396839 / 500000000000000000)) * (126 / 100) +
          2 * (((781396839 / 500000000000000000)) ^ 2 + 2 * ((585549491 / 125000000000000000)) * ((75123599 / 200000000000000000))) +
          6 * ((781396839 / 500000000000000000)) * ((75123599 / 200000000000000000)) * (126 / 100) + 8 * ((75123599 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12589) *
          (32 * (((585549491 / 125000000000000000) : ℝ) + (781396839 / 500000000000000000) + (75123599 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12589 : ℝ) ^ 16 *
      (d.w0 12589 162 + d.w1 12589 162 * √(π / 2) + 2 * d.w2 12589 162 +
        energyR16 12589 * radiusPolynomialRoot16 (d.w0 12589 162) (d.w1 12589 162)
          (d.w2 12589 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12589 : ℝ) ^ 16 *
        (((1882122207 / 100000000000000000000) : ℝ) + ((133909393 / 10000000000000000000)) * (126 / 100) + 2 * ((122317853 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12589) *
          (32 * (((1882122207 / 100000000000000000000) : ℝ) + (133909393 / 10000000000000000000) + (122317853 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12589

/-! A coarse bound on the actual paper statistics constant at dimension 12590. -/
namespace BstLean.Part266.Row12590
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12588 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12588 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12588 128 ≤ (12842 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12842 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12590) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12590 : ℕ))
    (by norm_num : (12590 : ℕ) ≤ 16384)
  have ht : paperTail256 12590 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12590 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12590 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12590 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12590 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12590 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12588 128 * √(2 / (12590 : ℝ)) *
      (√(12590 : ℝ) + paperT0 12590 + paperTail256 12590) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12590 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12590 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12590 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12588 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12588 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12590 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12590

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12590
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12590 (61 / 100) 162 (17 / (100 * 12590)) (26 / (10 * 12590)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12590 (61 / 100) 162 (17 / (100 * 12590)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (489149511 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1554089017 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2743719589 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12590 / 12590 * (61 / 100)) ^ 4 * inverseRadius8 (12590 - 1) /
            envelopeGap 12590 (61 / 100) 162 (17 / (100 * 12590)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12590

namespace BstLean.Part266.Row12590
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12590 162 ≤ (2341732977 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12590 162 ≤ (781241701 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (187771707 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12590 162 ≤ (940836891 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12590 162 ≤ (669387437 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12590 162 ≤ (489154827 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (489149511 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (489149511 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1554089017 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2743719589 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((918653 / 250000000) : ℝ) ≤ √(17 / (100 * 12590) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12590) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2211672469 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19710967867 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12590) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12590) ≤ (56164161 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12590) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12590 * (162 : ℝ) ^ 2 + 26 / (10 * 12590) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12590) : ℝ)) (tA 12590 * 162 ^ 2 + 26 / (10 * 12590)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((918653 / 250000000))) * ((489149511 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((918653 / 250000000)) ^ 3) * ((1554089017 / 1000000000000000000000000))) + ((2743719589 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((918653 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12590) : ℝ)) d.D d.V d.P (√(tA 12590) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((918653 / 250000000)) ^ 2 * (((2211672469 / 1000000000000000)) * ((19710967867 / 500000000000000000)))) + ((2743719589 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12590) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((918653 / 250000000)) * ((489149511 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12590) : ℝ)) (tA 12590 * 162 ^ 2 + 26 / (10 * 12590)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((489149511 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((918653 / 250000000)) ^ 2) * ((1554089017 / 1000000000000000000000000)) + ((2743719589 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12590) : ℝ)) (√(26 / (10 * 12590) : ℝ)) d.D d.V d.P (√(tA 12590) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((918653 / 250000000)) * (((2211672469 / 1000000000000000)) * ((19710967867 / 500000000000000000))) + ((2743719589 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12590) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((489149511 / 100000000000000000000) : ℝ) + ((2743719589 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12590

namespace BstLean.Part266.Row12590
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12590 162 ∧
    0 ≤ (tableEnvelope C).f1 12590 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12590 162 ∧
    0 ≤ (tableEnvelope C).w1 12590 162 ∧ 0 ≤ (tableEnvelope C).w2 12590 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12590 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12590 162 ∧ 0 ≤ d.f1 12590 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12590 162 ∧ 0 ≤ d.w1 12590 162 ∧ 0 ≤ d.w2 12590 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12590 ≤ 2 * (228 / 100 : ℝ) / 12590 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12590 ≤ 2 * (370 / 100 : ℝ) / 12590 := by
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
    (completeRAData (tableEnvelope C) 12590 162).locationBound 12590 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12590 162).energyBound 12590 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12590 162) (d.f1 12590 162) d.f2 ≤
      32 * (((2341732977 / 500000000000000000) : ℝ) + (781241701 / 500000000000000000) + (187771707 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12590 162) (d.w1 12590 162)
      (d.w2 12590 162) ≤
      32 * (((940836891 / 50000000000000000000) : ℝ) + (669387437 / 50000000000000000000) + (489154827 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12590 162) (d.f1 12590 162) d.f2 ≤
      ((2341732977 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2341732977 / 500000000000000000)) * ((781241701 / 500000000000000000)) * (126 / 100) +
      2 * (((781241701 / 500000000000000000)) ^ 2 + 2 * ((2341732977 / 500000000000000000)) * ((187771707 / 500000000000000000))) +
      6 * ((781241701 / 500000000000000000)) * ((187771707 / 500000000000000000)) * (126 / 100) + 8 * ((187771707 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12590 162) (d.f1 12590 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12590 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12590 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12590 162) (d.f1 12590 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12590 162) (d.w1 12590 162) (d.w2 12590 162)
  have hwexpr0 : 0 ≤ d.w0 12590 162 + d.w1 12590 162 * √(π / 2) +
      2 * d.w2 12590 162 + energyR16 12590 *
      radiusPolynomialRoot16 (d.w0 12590 162) (d.w1 12590 162) (d.w2 12590 162) := by
    positivity
  constructor
  · change (12590 : ℝ) ^ 8 * (mA 12590 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12590 162) (d.f1 12590 162) d.f2 + locationR16 12590 *
        radiusPolynomialRoot16 (d.f0 12590 162) (d.f1 12590 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12590 : ℝ) ^ 8 * (mA 12590 : ℝ) ^ 8 *
        ((((2341732977 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2341732977 / 500000000000000000)) * ((781241701 / 500000000000000000)) * (126 / 100) +
          2 * (((781241701 / 500000000000000000)) ^ 2 + 2 * ((2341732977 / 500000000000000000)) * ((187771707 / 500000000000000000))) +
          6 * ((781241701 / 500000000000000000)) * ((187771707 / 500000000000000000)) * (126 / 100) + 8 * ((187771707 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12590) *
          (32 * (((2341732977 / 500000000000000000) : ℝ) + (781241701 / 500000000000000000) + (187771707 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12590 : ℝ) ^ 16 *
      (d.w0 12590 162 + d.w1 12590 162 * √(π / 2) + 2 * d.w2 12590 162 +
        energyR16 12590 * radiusPolynomialRoot16 (d.w0 12590 162) (d.w1 12590 162)
          (d.w2 12590 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12590 : ℝ) ^ 16 *
        (((940836891 / 50000000000000000000) : ℝ) + ((669387437 / 50000000000000000000)) * (126 / 100) + 2 * ((489154827 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12590) *
          (32 * (((940836891 / 50000000000000000000) : ℝ) + (669387437 / 50000000000000000000) + (489154827 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12590

/-! A coarse bound on the actual paper statistics constant at dimension 12591. -/
namespace BstLean.Part266.Row12591
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12589 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12589 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12589 128 ≤ (12843 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12843 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12591) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12591 : ℕ))
    (by norm_num : (12591 : ℕ) ≤ 16384)
  have ht : paperTail256 12591 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12591 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12591 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12591 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12591 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12591 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12589 128 * √(2 / (12591 : ℝ)) *
      (√(12591 : ℝ) + paperT0 12591 + paperTail256 12591) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12591 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12591 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12591 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12589 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12589 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12591 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12591

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12591
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12591 (61 / 100) 162 (17 / (100 * 12591)) (26 / (10 * 12591)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12591 (61 / 100) 162 (17 / (100 * 12591)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (489032967 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (776797671 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1370979863 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12591 / 12591 * (61 / 100)) ^ 4 * inverseRadius8 (12591 - 1) /
            envelopeGap 12591 (61 / 100) 162 (17 / (100 * 12591)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12591

namespace BstLean.Part266.Row12591
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12591 162 ≤ (4682536303 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12591 162 ≤ (1562173227 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (46933607 / 125000000000000000)
  w0 : (tableEnvelope C).w0 12591 162 ≤ (1881225513 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12591 162 ≤ (669227963 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12591 162 ≤ (12225957 / 2500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (489032967 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (489032967 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (776797671 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1370979863 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1837233 / 500000000) : ℝ) ≤ √(17 / (100 * 12591) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12591) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2211408979 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9853918453 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12591) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12591) ≤ (561597 / 5000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12591) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12591 * (162 : ℝ) ^ 2 + 26 / (10 * 12591) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12591) : ℝ)) (tA 12591 * 162 ^ 2 + 26 / (10 * 12591)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1837233 / 500000000))) * ((489032967 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1837233 / 500000000)) ^ 3) * ((776797671 / 500000000000000000000000))) + ((1370979863 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1837233 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12591) : ℝ)) d.D d.V d.P (√(tA 12591) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1837233 / 500000000)) ^ 2 * (((2211408979 / 1000000000000000)) * ((9853918453 / 250000000000000000)))) + ((1370979863 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12591) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1837233 / 500000000)) * ((489032967 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12591) : ℝ)) (tA 12591 * 162 ^ 2 + 26 / (10 * 12591)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((489032967 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1837233 / 500000000)) ^ 2) * ((776797671 / 500000000000000000000000)) + ((1370979863 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12591) : ℝ)) (√(26 / (10 * 12591) : ℝ)) d.D d.V d.P (√(tA 12591) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1837233 / 500000000)) * (((2211408979 / 1000000000000000)) * ((9853918453 / 250000000000000000))) + ((1370979863 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12591) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((489032967 / 100000000000000000000) : ℝ) + ((1370979863 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12591

namespace BstLean.Part266.Row12591
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12591 162 ∧
    0 ≤ (tableEnvelope C).f1 12591 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12591 162 ∧
    0 ≤ (tableEnvelope C).w1 12591 162 ∧ 0 ≤ (tableEnvelope C).w2 12591 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12591 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12591 162 ∧ 0 ≤ d.f1 12591 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12591 162 ∧ 0 ≤ d.w1 12591 162 ∧ 0 ≤ d.w2 12591 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12591 ≤ 2 * (228 / 100 : ℝ) / 12591 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12591 ≤ 2 * (370 / 100 : ℝ) / 12591 := by
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
    (completeRAData (tableEnvelope C) 12591 162).locationBound 12591 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12591 162).energyBound 12591 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12591 162) (d.f1 12591 162) d.f2 ≤
      32 * (((4682536303 / 1000000000000000000) : ℝ) + (1562173227 / 1000000000000000000) + (46933607 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12591 162) (d.w1 12591 162)
      (d.w2 12591 162) ≤
      32 * (((1881225513 / 100000000000000000000) : ℝ) + (669227963 / 50000000000000000000) + (12225957 / 2500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12591 162) (d.f1 12591 162) d.f2 ≤
      ((4682536303 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4682536303 / 1000000000000000000)) * ((1562173227 / 1000000000000000000)) * (126 / 100) +
      2 * (((1562173227 / 1000000000000000000)) ^ 2 + 2 * ((4682536303 / 1000000000000000000)) * ((46933607 / 125000000000000000))) +
      6 * ((1562173227 / 1000000000000000000)) * ((46933607 / 125000000000000000)) * (126 / 100) + 8 * ((46933607 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12591 162) (d.f1 12591 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12591 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12591 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12591 162) (d.f1 12591 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12591 162) (d.w1 12591 162) (d.w2 12591 162)
  have hwexpr0 : 0 ≤ d.w0 12591 162 + d.w1 12591 162 * √(π / 2) +
      2 * d.w2 12591 162 + energyR16 12591 *
      radiusPolynomialRoot16 (d.w0 12591 162) (d.w1 12591 162) (d.w2 12591 162) := by
    positivity
  constructor
  · change (12591 : ℝ) ^ 8 * (mA 12591 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12591 162) (d.f1 12591 162) d.f2 + locationR16 12591 *
        radiusPolynomialRoot16 (d.f0 12591 162) (d.f1 12591 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12591 : ℝ) ^ 8 * (mA 12591 : ℝ) ^ 8 *
        ((((4682536303 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4682536303 / 1000000000000000000)) * ((1562173227 / 1000000000000000000)) * (126 / 100) +
          2 * (((1562173227 / 1000000000000000000)) ^ 2 + 2 * ((4682536303 / 1000000000000000000)) * ((46933607 / 125000000000000000))) +
          6 * ((1562173227 / 1000000000000000000)) * ((46933607 / 125000000000000000)) * (126 / 100) + 8 * ((46933607 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12591) *
          (32 * (((4682536303 / 1000000000000000000) : ℝ) + (1562173227 / 1000000000000000000) + (46933607 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12591 : ℝ) ^ 16 *
      (d.w0 12591 162 + d.w1 12591 162 * √(π / 2) + 2 * d.w2 12591 162 +
        energyR16 12591 * radiusPolynomialRoot16 (d.w0 12591 162) (d.w1 12591 162)
          (d.w2 12591 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12591 : ℝ) ^ 16 *
        (((1881225513 / 100000000000000000000) : ℝ) + ((669227963 / 50000000000000000000)) * (126 / 100) + 2 * ((12225957 / 2500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12591) *
          (32 * (((1881225513 / 100000000000000000000) : ℝ) + (669227963 / 50000000000000000000) + (12225957 / 2500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12591

/-! A coarse bound on the actual paper statistics constant at dimension 12592. -/
namespace BstLean.Part266.Row12592
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12590 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12590 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12590 128 ≤ (12844 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12844 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12592) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12592 : ℕ))
    (by norm_num : (12592 : ℕ) ≤ 16384)
  have ht : paperTail256 12592 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12592 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12592 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12592 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12592 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12592 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12590 128 * √(2 / (12592 : ℝ)) *
      (√(12592 : ℝ) + paperT0 12592 + paperTail256 12592) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12592 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12592 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12592 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12590 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12590 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12592 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12592

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12592
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12592 (61 / 100) 162 (17 / (100 * 12592)) (26 / (10 * 12592)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12592 (61 / 100) 162 (17 / (100 * 12592)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (488916459 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1553101863 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1370100567 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12592 / 12592 * (61 / 100)) ^ 4 * inverseRadius8 (12592 - 1) /
            envelopeGap 12592 (61 / 100) 162 (17 / (100 * 12592)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12592

namespace BstLean.Part266.Row12592
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12592 162 ≤ (146300103 / 31250000000000000)
  f1 : (tableEnvelope C).f1 12592 162 ≤ (15618623 / 10000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (375394217 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12592 162 ≤ (1880776641 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12592 162 ≤ (16726709 / 1250000000000000000)
  w2 : (tableEnvelope C).w2 12592 162 ≤ (61115221 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (488916459 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (488916459 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1553101863 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1370100567 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3674321 / 1000000000) : ℝ) ≤ √(17 / (100 * 12592) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12592) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1105572769 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39409413381 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12592) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12592) ≤ (1403881 / 12500000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12592) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12592 * (162 : ℝ) ^ 2 + 26 / (10 * 12592) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12592) : ℝ)) (tA 12592 * 162 ^ 2 + 26 / (10 * 12592)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3674321 / 1000000000))) * ((488916459 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3674321 / 1000000000)) ^ 3) * ((1553101863 / 1000000000000000000000000))) + ((1370100567 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3674321 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12592) : ℝ)) d.D d.V d.P (√(tA 12592) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3674321 / 1000000000)) ^ 2 * (((1105572769 / 500000000000000)) * ((39409413381 / 1000000000000000000)))) + ((1370100567 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12592) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3674321 / 1000000000)) * ((488916459 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12592) : ℝ)) (tA 12592 * 162 ^ 2 + 26 / (10 * 12592)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((488916459 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3674321 / 1000000000)) ^ 2) * ((1553101863 / 1000000000000000000000000)) + ((1370100567 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12592) : ℝ)) (√(26 / (10 * 12592) : ℝ)) d.D d.V d.P (√(tA 12592) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3674321 / 1000000000)) * (((1105572769 / 500000000000000)) * ((39409413381 / 1000000000000000000))) + ((1370100567 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12592) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((488916459 / 100000000000000000000) : ℝ) + ((1370100567 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12592

namespace BstLean.Part266.Row12592
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12592 162 ∧
    0 ≤ (tableEnvelope C).f1 12592 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12592 162 ∧
    0 ≤ (tableEnvelope C).w1 12592 162 ∧ 0 ≤ (tableEnvelope C).w2 12592 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12592 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12592 162 ∧ 0 ≤ d.f1 12592 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12592 162 ∧ 0 ≤ d.w1 12592 162 ∧ 0 ≤ d.w2 12592 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12592 ≤ 2 * (228 / 100 : ℝ) / 12592 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12592 ≤ 2 * (370 / 100 : ℝ) / 12592 := by
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
    (completeRAData (tableEnvelope C) 12592 162).locationBound 12592 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12592 162).energyBound 12592 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12592 162) (d.f1 12592 162) d.f2 ≤
      32 * (((146300103 / 31250000000000000) : ℝ) + (15618623 / 10000000000000000) + (375394217 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12592 162) (d.w1 12592 162)
      (d.w2 12592 162) ≤
      32 * (((1880776641 / 100000000000000000000) : ℝ) + (16726709 / 1250000000000000000) + (61115221 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12592 162) (d.f1 12592 162) d.f2 ≤
      ((146300103 / 31250000000000000) : ℝ) ^ 2 + 2 * ((146300103 / 31250000000000000)) * ((15618623 / 10000000000000000)) * (126 / 100) +
      2 * (((15618623 / 10000000000000000)) ^ 2 + 2 * ((146300103 / 31250000000000000)) * ((375394217 / 1000000000000000000))) +
      6 * ((15618623 / 10000000000000000)) * ((375394217 / 1000000000000000000)) * (126 / 100) + 8 * ((375394217 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12592 162) (d.f1 12592 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12592 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12592 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12592 162) (d.f1 12592 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12592 162) (d.w1 12592 162) (d.w2 12592 162)
  have hwexpr0 : 0 ≤ d.w0 12592 162 + d.w1 12592 162 * √(π / 2) +
      2 * d.w2 12592 162 + energyR16 12592 *
      radiusPolynomialRoot16 (d.w0 12592 162) (d.w1 12592 162) (d.w2 12592 162) := by
    positivity
  constructor
  · change (12592 : ℝ) ^ 8 * (mA 12592 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12592 162) (d.f1 12592 162) d.f2 + locationR16 12592 *
        radiusPolynomialRoot16 (d.f0 12592 162) (d.f1 12592 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12592 : ℝ) ^ 8 * (mA 12592 : ℝ) ^ 8 *
        ((((146300103 / 31250000000000000) : ℝ) ^ 2 + 2 * ((146300103 / 31250000000000000)) * ((15618623 / 10000000000000000)) * (126 / 100) +
          2 * (((15618623 / 10000000000000000)) ^ 2 + 2 * ((146300103 / 31250000000000000)) * ((375394217 / 1000000000000000000))) +
          6 * ((15618623 / 10000000000000000)) * ((375394217 / 1000000000000000000)) * (126 / 100) + 8 * ((375394217 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12592) *
          (32 * (((146300103 / 31250000000000000) : ℝ) + (15618623 / 10000000000000000) + (375394217 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12592 : ℝ) ^ 16 *
      (d.w0 12592 162 + d.w1 12592 162 * √(π / 2) + 2 * d.w2 12592 162 +
        energyR16 12592 * radiusPolynomialRoot16 (d.w0 12592 162) (d.w1 12592 162)
          (d.w2 12592 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12592 : ℝ) ^ 16 *
        (((1880776641 / 100000000000000000000) : ℝ) + ((16726709 / 1250000000000000000)) * (126 / 100) + 2 * ((61115221 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12592) *
          (32 * (((1880776641 / 100000000000000000000) : ℝ) + (16726709 / 1250000000000000000) + (61115221 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12592

/-! A coarse bound on the actual paper statistics constant at dimension 12593. -/
namespace BstLean.Part266.Row12593
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12591 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12591 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12591 128 ≤ (12845 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12845 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12593) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12593 : ℕ))
    (by norm_num : (12593 : ℕ) ≤ 16384)
  have ht : paperTail256 12593 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12593 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12593 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12593 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12593 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12593 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12591 128 * √(2 / (12593 : ℝ)) *
      (√(12593 : ℝ) + paperT0 12593 + paperTail256 12593) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12593 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12593 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12593 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12591 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12591 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12593 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12593

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12593
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12593 (61 / 100) 162 (17 / (100 * 12593)) (26 / (10 * 12593)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12593 (61 / 100) 162 (17 / (100 * 12593)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (488799989 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (77630429 / 50000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (43815101 / 8000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12593 / 12593 * (61 / 100)) ^ 4 * inverseRadius8 (12593 - 1) /
            envelopeGap 12593 (61 / 100) 162 (17 / (100 * 12593)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12593

namespace BstLean.Part266.Row12593
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12593 162 ≤ (468067429 / 100000000000000000)
  f1 : (tableEnvelope C).f1 12593 162 ≤ (1561552327 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (46914963 / 125000000000000000)
  w0 : (tableEnvelope C).w0 12593 162 ≤ (1880328683 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12593 162 ≤ (334454497 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12593 162 ≤ (97761059 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (488799989 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (488799989 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (77630429 / 50000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (43815101 / 8000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((146967 / 40000000) : ℝ) ≤ √(17 / (100 * 12593) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12593) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (276360269 / 125000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39403154443 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12593) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12593) ≤ (56150781 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12593) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12593 * (162 : ℝ) ^ 2 + 26 / (10 * 12593) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12593) : ℝ)) (tA 12593 * 162 ^ 2 + 26 / (10 * 12593)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((146967 / 40000000))) * ((488799989 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((146967 / 40000000)) ^ 3) * ((77630429 / 50000000000000000000000))) + ((43815101 / 8000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((146967 / 40000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12593) : ℝ)) d.D d.V d.P (√(tA 12593) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((146967 / 40000000)) ^ 2 * (((276360269 / 125000000000000)) * ((39403154443 / 1000000000000000000)))) + ((43815101 / 8000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12593) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((146967 / 40000000)) * ((488799989 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12593) : ℝ)) (tA 12593 * 162 ^ 2 + 26 / (10 * 12593)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((488799989 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((146967 / 40000000)) ^ 2) * ((77630429 / 50000000000000000000000)) + ((43815101 / 8000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12593) : ℝ)) (√(26 / (10 * 12593) : ℝ)) d.D d.V d.P (√(tA 12593) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((146967 / 40000000)) * (((276360269 / 125000000000000)) * ((39403154443 / 1000000000000000000))) + ((43815101 / 8000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12593) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((488799989 / 100000000000000000000) : ℝ) + ((43815101 / 8000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12593

namespace BstLean.Part266.Row12593
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12593 162 ∧
    0 ≤ (tableEnvelope C).f1 12593 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12593 162 ∧
    0 ≤ (tableEnvelope C).w1 12593 162 ∧ 0 ≤ (tableEnvelope C).w2 12593 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12593 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12593 162 ∧ 0 ≤ d.f1 12593 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12593 162 ∧ 0 ≤ d.w1 12593 162 ∧ 0 ≤ d.w2 12593 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12593 ≤ 2 * (228 / 100 : ℝ) / 12593 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12593 ≤ 2 * (370 / 100 : ℝ) / 12593 := by
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
    (completeRAData (tableEnvelope C) 12593 162).locationBound 12593 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12593 162).energyBound 12593 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12593 162) (d.f1 12593 162) d.f2 ≤
      32 * (((468067429 / 100000000000000000) : ℝ) + (1561552327 / 1000000000000000000) + (46914963 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12593 162) (d.w1 12593 162)
      (d.w2 12593 162) ≤
      32 * (((1880328683 / 100000000000000000000) : ℝ) + (334454497 / 25000000000000000000) + (97761059 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12593 162) (d.f1 12593 162) d.f2 ≤
      ((468067429 / 100000000000000000) : ℝ) ^ 2 + 2 * ((468067429 / 100000000000000000)) * ((1561552327 / 1000000000000000000)) * (126 / 100) +
      2 * (((1561552327 / 1000000000000000000)) ^ 2 + 2 * ((468067429 / 100000000000000000)) * ((46914963 / 125000000000000000))) +
      6 * ((1561552327 / 1000000000000000000)) * ((46914963 / 125000000000000000)) * (126 / 100) + 8 * ((46914963 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12593 162) (d.f1 12593 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12593 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12593 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12593 162) (d.f1 12593 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12593 162) (d.w1 12593 162) (d.w2 12593 162)
  have hwexpr0 : 0 ≤ d.w0 12593 162 + d.w1 12593 162 * √(π / 2) +
      2 * d.w2 12593 162 + energyR16 12593 *
      radiusPolynomialRoot16 (d.w0 12593 162) (d.w1 12593 162) (d.w2 12593 162) := by
    positivity
  constructor
  · change (12593 : ℝ) ^ 8 * (mA 12593 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12593 162) (d.f1 12593 162) d.f2 + locationR16 12593 *
        radiusPolynomialRoot16 (d.f0 12593 162) (d.f1 12593 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12593 : ℝ) ^ 8 * (mA 12593 : ℝ) ^ 8 *
        ((((468067429 / 100000000000000000) : ℝ) ^ 2 + 2 * ((468067429 / 100000000000000000)) * ((1561552327 / 1000000000000000000)) * (126 / 100) +
          2 * (((1561552327 / 1000000000000000000)) ^ 2 + 2 * ((468067429 / 100000000000000000)) * ((46914963 / 125000000000000000))) +
          6 * ((1561552327 / 1000000000000000000)) * ((46914963 / 125000000000000000)) * (126 / 100) + 8 * ((46914963 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12593) *
          (32 * (((468067429 / 100000000000000000) : ℝ) + (1561552327 / 1000000000000000000) + (46914963 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12593 : ℝ) ^ 16 *
      (d.w0 12593 162 + d.w1 12593 162 * √(π / 2) + 2 * d.w2 12593 162 +
        energyR16 12593 * radiusPolynomialRoot16 (d.w0 12593 162) (d.w1 12593 162)
          (d.w2 12593 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12593 : ℝ) ^ 16 *
        (((1880328683 / 100000000000000000000) : ℝ) + ((334454497 / 25000000000000000000)) * (126 / 100) + 2 * ((97761059 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12593) *
          (32 * (((1880328683 / 100000000000000000000) : ℝ) + (334454497 / 25000000000000000000) + (97761059 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12593

/-! A coarse bound on the actual paper statistics constant at dimension 12594. -/
namespace BstLean.Part266.Row12594
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12592 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12592 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12592 128 ≤ (12846 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12846 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12594) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12594 : ℕ))
    (by norm_num : (12594 : ℕ) ≤ 16384)
  have ht : paperTail256 12594 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12594 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12594 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12594 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12594 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12594 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12592 128 * √(2 / (12594 : ℝ)) *
      (√(12594 : ℝ) + paperT0 12594 + paperTail256 12594) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12594 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12594 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12594 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12592 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12592 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12594 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12594

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12594
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12594 (61 / 100) 162 (17 / (100 * 12594)) (26 / (10 * 12594)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12594 (61 / 100) 162 (17 / (100 * 12594)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (122170889 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1552115493 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5473375519 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12594 / 12594 * (61 / 100)) ^ 4 * inverseRadius8 (12594 - 1) /
            envelopeGap 12594 (61 / 100) 162 (17 / (100 * 12594)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12594

namespace BstLean.Part266.Row12594
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12594 162 ≤ (2339872803 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12594 162 ≤ (312248491 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (375245213 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12594 162 ≤ (23498511 / 1250000000000000000)
  w1 : (tableEnvelope C).w1 12594 162 ≤ (1337499363 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12594 162 ≤ (244344429 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (122170889 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (122170889 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1552115493 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5473375519 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3674029 / 1000000000) : ℝ) ≤ √(17 / (100 * 12594) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12594) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2210618819 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19698448499 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12594) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12594) ≤ (22458529 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12594) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12594 * (162 : ℝ) ^ 2 + 26 / (10 * 12594) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12594) : ℝ)) (tA 12594 * 162 ^ 2 + 26 / (10 * 12594)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3674029 / 1000000000))) * ((122170889 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3674029 / 1000000000)) ^ 3) * ((1552115493 / 1000000000000000000000000))) + ((5473375519 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3674029 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12594) : ℝ)) d.D d.V d.P (√(tA 12594) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3674029 / 1000000000)) ^ 2 * (((2210618819 / 1000000000000000)) * ((19698448499 / 500000000000000000)))) + ((5473375519 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12594) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3674029 / 1000000000)) * ((122170889 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12594) : ℝ)) (tA 12594 * 162 ^ 2 + 26 / (10 * 12594)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((122170889 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3674029 / 1000000000)) ^ 2) * ((1552115493 / 1000000000000000000000000)) + ((5473375519 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12594) : ℝ)) (√(26 / (10 * 12594) : ℝ)) d.D d.V d.P (√(tA 12594) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3674029 / 1000000000)) * (((2210618819 / 1000000000000000)) * ((19698448499 / 500000000000000000))) + ((5473375519 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12594) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((122170889 / 25000000000000000000) : ℝ) + ((5473375519 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12594

namespace BstLean.Part266.Row12594
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12594 162 ∧
    0 ≤ (tableEnvelope C).f1 12594 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12594 162 ∧
    0 ≤ (tableEnvelope C).w1 12594 162 ∧ 0 ≤ (tableEnvelope C).w2 12594 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12594 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12594 162 ∧ 0 ≤ d.f1 12594 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12594 162 ∧ 0 ≤ d.w1 12594 162 ∧ 0 ≤ d.w2 12594 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12594 ≤ 2 * (228 / 100 : ℝ) / 12594 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12594 ≤ 2 * (370 / 100 : ℝ) / 12594 := by
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
    (completeRAData (tableEnvelope C) 12594 162).locationBound 12594 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12594 162).energyBound 12594 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12594 162) (d.f1 12594 162) d.f2 ≤
      32 * (((2339872803 / 500000000000000000) : ℝ) + (312248491 / 200000000000000000) + (375245213 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12594 162) (d.w1 12594 162)
      (d.w2 12594 162) ≤
      32 * (((23498511 / 1250000000000000000) : ℝ) + (1337499363 / 100000000000000000000) + (244344429 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12594 162) (d.f1 12594 162) d.f2 ≤
      ((2339872803 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2339872803 / 500000000000000000)) * ((312248491 / 200000000000000000)) * (126 / 100) +
      2 * (((312248491 / 200000000000000000)) ^ 2 + 2 * ((2339872803 / 500000000000000000)) * ((375245213 / 1000000000000000000))) +
      6 * ((312248491 / 200000000000000000)) * ((375245213 / 1000000000000000000)) * (126 / 100) + 8 * ((375245213 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12594 162) (d.f1 12594 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12594 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12594 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12594 162) (d.f1 12594 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12594 162) (d.w1 12594 162) (d.w2 12594 162)
  have hwexpr0 : 0 ≤ d.w0 12594 162 + d.w1 12594 162 * √(π / 2) +
      2 * d.w2 12594 162 + energyR16 12594 *
      radiusPolynomialRoot16 (d.w0 12594 162) (d.w1 12594 162) (d.w2 12594 162) := by
    positivity
  constructor
  · change (12594 : ℝ) ^ 8 * (mA 12594 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12594 162) (d.f1 12594 162) d.f2 + locationR16 12594 *
        radiusPolynomialRoot16 (d.f0 12594 162) (d.f1 12594 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12594 : ℝ) ^ 8 * (mA 12594 : ℝ) ^ 8 *
        ((((2339872803 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2339872803 / 500000000000000000)) * ((312248491 / 200000000000000000)) * (126 / 100) +
          2 * (((312248491 / 200000000000000000)) ^ 2 + 2 * ((2339872803 / 500000000000000000)) * ((375245213 / 1000000000000000000))) +
          6 * ((312248491 / 200000000000000000)) * ((375245213 / 1000000000000000000)) * (126 / 100) + 8 * ((375245213 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12594) *
          (32 * (((2339872803 / 500000000000000000) : ℝ) + (312248491 / 200000000000000000) + (375245213 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12594 : ℝ) ^ 16 *
      (d.w0 12594 162 + d.w1 12594 162 * √(π / 2) + 2 * d.w2 12594 162 +
        energyR16 12594 * radiusPolynomialRoot16 (d.w0 12594 162) (d.w1 12594 162)
          (d.w2 12594 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12594 : ℝ) ^ 16 *
        (((23498511 / 1250000000000000000) : ℝ) + ((1337499363 / 100000000000000000000)) * (126 / 100) + 2 * ((244344429 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12594) *
          (32 * (((23498511 / 1250000000000000000) : ℝ) + (1337499363 / 100000000000000000000) + (244344429 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12594

/-! A coarse bound on the actual paper statistics constant at dimension 12595. -/
namespace BstLean.Part266.Row12595
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12593 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12593 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12593 128 ≤ (12847 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12847 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12595) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12595 : ℕ))
    (by norm_num : (12595 : ℕ) ≤ 16384)
  have ht : paperTail256 12595 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12595 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12595 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12595 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12595 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12595 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12593 128 * √(2 / (12595 : ℝ)) *
      (√(12595 : ℝ) + paperT0 12595 + paperTail256 12595) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12595 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12595 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12595 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12593 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12593 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12595 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12595

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12595
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12595 (61 / 100) 162 (17 / (100 * 12595)) (26 / (10 * 12595)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12595 (61 / 100) 162 (17 / (100 * 12595)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (488567159 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1551622601 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (109397319 / 20000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12595 / 12595 * (61 / 100)) ^ 4 * inverseRadius8 (12595 - 1) /
            envelopeGap 12595 (61 / 100) 162 (17 / (100 * 12595)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12595

namespace BstLean.Part266.Row12595
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12595 162 ≤ (2339408621 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12595 162 ≤ (780466341 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (46896343 / 125000000000000000)
  w0 : (tableEnvelope C).w0 12595 162 ≤ (1879433231 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12595 162 ≤ (334295211 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12595 162 ≤ (244286229 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (488567159 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (488567159 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1551622601 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (109397319 / 20000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3673883 / 1000000000) : ℝ) ≤ √(17 / (100 * 12595) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12595) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (442071107 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19695320517 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12595) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12595) ≤ (112283729 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12595) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12595 * (162 : ℝ) ^ 2 + 26 / (10 * 12595) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12595) : ℝ)) (tA 12595 * 162 ^ 2 + 26 / (10 * 12595)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3673883 / 1000000000))) * ((488567159 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3673883 / 1000000000)) ^ 3) * ((1551622601 / 1000000000000000000000000))) + ((109397319 / 20000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3673883 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12595) : ℝ)) d.D d.V d.P (√(tA 12595) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3673883 / 1000000000)) ^ 2 * (((442071107 / 200000000000000)) * ((19695320517 / 500000000000000000)))) + ((109397319 / 20000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12595) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3673883 / 1000000000)) * ((488567159 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12595) : ℝ)) (tA 12595 * 162 ^ 2 + 26 / (10 * 12595)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((488567159 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3673883 / 1000000000)) ^ 2) * ((1551622601 / 1000000000000000000000000)) + ((109397319 / 20000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12595) : ℝ)) (√(26 / (10 * 12595) : ℝ)) d.D d.V d.P (√(tA 12595) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3673883 / 1000000000)) * (((442071107 / 200000000000000)) * ((19695320517 / 500000000000000000))) + ((109397319 / 20000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12595) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((488567159 / 100000000000000000000) : ℝ) + ((109397319 / 20000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12595

namespace BstLean.Part266.Row12595
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12595 162 ∧
    0 ≤ (tableEnvelope C).f1 12595 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12595 162 ∧
    0 ≤ (tableEnvelope C).w1 12595 162 ∧ 0 ≤ (tableEnvelope C).w2 12595 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12595 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12595 162 ∧ 0 ≤ d.f1 12595 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12595 162 ∧ 0 ≤ d.w1 12595 162 ∧ 0 ≤ d.w2 12595 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12595 ≤ 2 * (228 / 100 : ℝ) / 12595 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12595 ≤ 2 * (370 / 100 : ℝ) / 12595 := by
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
    (completeRAData (tableEnvelope C) 12595 162).locationBound 12595 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12595 162).energyBound 12595 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12595 162) (d.f1 12595 162) d.f2 ≤
      32 * (((2339408621 / 500000000000000000) : ℝ) + (780466341 / 500000000000000000) + (46896343 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12595 162) (d.w1 12595 162)
      (d.w2 12595 162) ≤
      32 * (((1879433231 / 100000000000000000000) : ℝ) + (334295211 / 25000000000000000000) + (244286229 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12595 162) (d.f1 12595 162) d.f2 ≤
      ((2339408621 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2339408621 / 500000000000000000)) * ((780466341 / 500000000000000000)) * (126 / 100) +
      2 * (((780466341 / 500000000000000000)) ^ 2 + 2 * ((2339408621 / 500000000000000000)) * ((46896343 / 125000000000000000))) +
      6 * ((780466341 / 500000000000000000)) * ((46896343 / 125000000000000000)) * (126 / 100) + 8 * ((46896343 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12595 162) (d.f1 12595 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12595 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12595 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12595 162) (d.f1 12595 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12595 162) (d.w1 12595 162) (d.w2 12595 162)
  have hwexpr0 : 0 ≤ d.w0 12595 162 + d.w1 12595 162 * √(π / 2) +
      2 * d.w2 12595 162 + energyR16 12595 *
      radiusPolynomialRoot16 (d.w0 12595 162) (d.w1 12595 162) (d.w2 12595 162) := by
    positivity
  constructor
  · change (12595 : ℝ) ^ 8 * (mA 12595 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12595 162) (d.f1 12595 162) d.f2 + locationR16 12595 *
        radiusPolynomialRoot16 (d.f0 12595 162) (d.f1 12595 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12595 : ℝ) ^ 8 * (mA 12595 : ℝ) ^ 8 *
        ((((2339408621 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2339408621 / 500000000000000000)) * ((780466341 / 500000000000000000)) * (126 / 100) +
          2 * (((780466341 / 500000000000000000)) ^ 2 + 2 * ((2339408621 / 500000000000000000)) * ((46896343 / 125000000000000000))) +
          6 * ((780466341 / 500000000000000000)) * ((46896343 / 125000000000000000)) * (126 / 100) + 8 * ((46896343 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12595) *
          (32 * (((2339408621 / 500000000000000000) : ℝ) + (780466341 / 500000000000000000) + (46896343 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12595 : ℝ) ^ 16 *
      (d.w0 12595 162 + d.w1 12595 162 * √(π / 2) + 2 * d.w2 12595 162 +
        energyR16 12595 * radiusPolynomialRoot16 (d.w0 12595 162) (d.w1 12595 162)
          (d.w2 12595 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12595 : ℝ) ^ 16 *
        (((1879433231 / 100000000000000000000) : ℝ) + ((334295211 / 25000000000000000000)) * (126 / 100) + 2 * ((244286229 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12595) *
          (32 * (((1879433231 / 100000000000000000000) : ℝ) + (334295211 / 25000000000000000000) + (244286229 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12595

/-! A coarse bound on the actual paper statistics constant at dimension 12596. -/
namespace BstLean.Part266.Row12596
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12594 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12594 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12594 128 ≤ (12848 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12848 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12596) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12596 : ℕ))
    (by norm_num : (12596 : ℕ) ≤ 16384)
  have ht : paperTail256 12596 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12596 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12596 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12596 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12596 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12596 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12594 128 * √(2 / (12596 : ℝ)) *
      (√(12596 : ℝ) + paperT0 12596 + paperTail256 12596) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12596 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12596 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12596 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12594 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12594 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12596 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12596

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12596
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12596 (61 / 100) 162 (17 / (100 * 12596)) (26 / (10 * 12596)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12596 (61 / 100) 162 (17 / (100 * 12596)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (1221127 / 250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (310225981 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2733179457 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12596 / 12596 * (61 / 100)) ^ 4 * inverseRadius8 (12596 - 1) /
            envelopeGap 12596 (61 / 100) 162 (17 / (100 * 12596)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12596

namespace BstLean.Part266.Row12596
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12596 162 ≤ (4677889201 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12596 162 ≤ (1560623011 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (375096299 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12596 162 ≤ (1878985739 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12596 162 ≤ (668431217 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12596 162 ≤ (15264253 / 3125000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (1221127 / 250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (1221127 / 250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (310225981 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2733179457 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3673737 / 1000000000) : ℝ) ≤ √(17 / (100 * 12596) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12596) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1105046153 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9846096641 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12596) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12596) ≤ (22454963 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12596) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12596 * (162 : ℝ) ^ 2 + 26 / (10 * 12596) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12596) : ℝ)) (tA 12596 * 162 ^ 2 + 26 / (10 * 12596)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3673737 / 1000000000))) * ((1221127 / 250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3673737 / 1000000000)) ^ 3) * ((310225981 / 200000000000000000000000))) + ((2733179457 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3673737 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12596) : ℝ)) d.D d.V d.P (√(tA 12596) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3673737 / 1000000000)) ^ 2 * (((1105046153 / 500000000000000)) * ((9846096641 / 250000000000000000)))) + ((2733179457 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12596) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3673737 / 1000000000)) * ((1221127 / 250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12596) : ℝ)) (tA 12596 * 162 ^ 2 + 26 / (10 * 12596)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((1221127 / 250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3673737 / 1000000000)) ^ 2) * ((310225981 / 200000000000000000000000)) + ((2733179457 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12596) : ℝ)) (√(26 / (10 * 12596) : ℝ)) d.D d.V d.P (√(tA 12596) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3673737 / 1000000000)) * (((1105046153 / 500000000000000)) * ((9846096641 / 250000000000000000))) + ((2733179457 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12596) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((1221127 / 250000000000000000) : ℝ) + ((2733179457 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12596

namespace BstLean.Part266.Row12596
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12596 162 ∧
    0 ≤ (tableEnvelope C).f1 12596 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12596 162 ∧
    0 ≤ (tableEnvelope C).w1 12596 162 ∧ 0 ≤ (tableEnvelope C).w2 12596 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12596 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12596 162 ∧ 0 ≤ d.f1 12596 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12596 162 ∧ 0 ≤ d.w1 12596 162 ∧ 0 ≤ d.w2 12596 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12596 ≤ 2 * (228 / 100 : ℝ) / 12596 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12596 ≤ 2 * (370 / 100 : ℝ) / 12596 := by
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
    (completeRAData (tableEnvelope C) 12596 162).locationBound 12596 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12596 162).energyBound 12596 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12596 162) (d.f1 12596 162) d.f2 ≤
      32 * (((4677889201 / 1000000000000000000) : ℝ) + (1560623011 / 1000000000000000000) + (375096299 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12596 162) (d.w1 12596 162)
      (d.w2 12596 162) ≤
      32 * (((1878985739 / 100000000000000000000) : ℝ) + (668431217 / 50000000000000000000) + (15264253 / 3125000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12596 162) (d.f1 12596 162) d.f2 ≤
      ((4677889201 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4677889201 / 1000000000000000000)) * ((1560623011 / 1000000000000000000)) * (126 / 100) +
      2 * (((1560623011 / 1000000000000000000)) ^ 2 + 2 * ((4677889201 / 1000000000000000000)) * ((375096299 / 1000000000000000000))) +
      6 * ((1560623011 / 1000000000000000000)) * ((375096299 / 1000000000000000000)) * (126 / 100) + 8 * ((375096299 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12596 162) (d.f1 12596 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12596 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12596 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12596 162) (d.f1 12596 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12596 162) (d.w1 12596 162) (d.w2 12596 162)
  have hwexpr0 : 0 ≤ d.w0 12596 162 + d.w1 12596 162 * √(π / 2) +
      2 * d.w2 12596 162 + energyR16 12596 *
      radiusPolynomialRoot16 (d.w0 12596 162) (d.w1 12596 162) (d.w2 12596 162) := by
    positivity
  constructor
  · change (12596 : ℝ) ^ 8 * (mA 12596 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12596 162) (d.f1 12596 162) d.f2 + locationR16 12596 *
        radiusPolynomialRoot16 (d.f0 12596 162) (d.f1 12596 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12596 : ℝ) ^ 8 * (mA 12596 : ℝ) ^ 8 *
        ((((4677889201 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4677889201 / 1000000000000000000)) * ((1560623011 / 1000000000000000000)) * (126 / 100) +
          2 * (((1560623011 / 1000000000000000000)) ^ 2 + 2 * ((4677889201 / 1000000000000000000)) * ((375096299 / 1000000000000000000))) +
          6 * ((1560623011 / 1000000000000000000)) * ((375096299 / 1000000000000000000)) * (126 / 100) + 8 * ((375096299 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12596) *
          (32 * (((4677889201 / 1000000000000000000) : ℝ) + (1560623011 / 1000000000000000000) + (375096299 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12596 : ℝ) ^ 16 *
      (d.w0 12596 162 + d.w1 12596 162 * √(π / 2) + 2 * d.w2 12596 162 +
        energyR16 12596 * radiusPolynomialRoot16 (d.w0 12596 162) (d.w1 12596 162)
          (d.w2 12596 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12596 : ℝ) ^ 16 *
        (((1878985739 / 100000000000000000000) : ℝ) + ((668431217 / 50000000000000000000)) * (126 / 100) + 2 * ((15264253 / 3125000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12596) *
          (32 * (((1878985739 / 100000000000000000000) : ℝ) + (668431217 / 50000000000000000000) + (15264253 / 3125000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12596

/-! A coarse bound on the actual paper statistics constant at dimension 12597. -/
namespace BstLean.Part266.Row12597
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12595 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12595 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12595 128 ≤ (12849 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12849 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12597) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12597 : ℕ))
    (by norm_num : (12597 : ℕ) ≤ 16384)
  have ht : paperTail256 12597 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12597 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12597 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12597 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12597 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12597 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12595 128 * √(2 / (12597 : ℝ)) *
      (√(12597 : ℝ) + paperT0 12597 + paperTail256 12597) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12597 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12597 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12597 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12595 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12595 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12597 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12597

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12597
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12597 (61 / 100) 162 (17 / (100 * 12597)) (26 / (10 * 12597)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12597 (61 / 100) 162 (17 / (100 * 12597)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (244167239 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (310127481 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5462854411 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12597 / 12597 * (61 / 100)) ^ 4 * inverseRadius8 (12597 - 1) /
            envelopeGap 12597 (61 / 100) 162 (17 / (100 * 12597)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12597

namespace BstLean.Part266.Row12597
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12597 162 ≤ (4676961483 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12597 162 ≤ (780156721 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (120007 / 320000000000000)
  w0 : (tableEnvelope C).w0 12597 162 ≤ (1878538403 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12597 162 ≤ (334136033 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12597 162 ≤ (48833977 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (244167239 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (244167239 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (310127481 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5462854411 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3673591 / 1000000000) : ℝ) ≤ √(17 / (100 * 12597) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12597) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (220982913 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3937813359 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12597) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12597) ≤ (56132951 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12597) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12597 * (162 : ℝ) ^ 2 + 26 / (10 * 12597) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12597) : ℝ)) (tA 12597 * 162 ^ 2 + 26 / (10 * 12597)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3673591 / 1000000000))) * ((244167239 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3673591 / 1000000000)) ^ 3) * ((310127481 / 200000000000000000000000))) + ((5462854411 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3673591 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12597) : ℝ)) d.D d.V d.P (√(tA 12597) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3673591 / 1000000000)) ^ 2 * (((220982913 / 100000000000000)) * ((3937813359 / 100000000000000000)))) + ((5462854411 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12597) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3673591 / 1000000000)) * ((244167239 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12597) : ℝ)) (tA 12597 * 162 ^ 2 + 26 / (10 * 12597)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((244167239 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3673591 / 1000000000)) ^ 2) * ((310127481 / 200000000000000000000000)) + ((5462854411 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12597) : ℝ)) (√(26 / (10 * 12597) : ℝ)) d.D d.V d.P (√(tA 12597) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3673591 / 1000000000)) * (((220982913 / 100000000000000)) * ((3937813359 / 100000000000000000))) + ((5462854411 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12597) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((244167239 / 50000000000000000000) : ℝ) + ((5462854411 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12597

namespace BstLean.Part266.Row12597
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12597 162 ∧
    0 ≤ (tableEnvelope C).f1 12597 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12597 162 ∧
    0 ≤ (tableEnvelope C).w1 12597 162 ∧ 0 ≤ (tableEnvelope C).w2 12597 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12597 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12597 162 ∧ 0 ≤ d.f1 12597 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12597 162 ∧ 0 ≤ d.w1 12597 162 ∧ 0 ≤ d.w2 12597 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12597 ≤ 2 * (228 / 100 : ℝ) / 12597 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12597 ≤ 2 * (370 / 100 : ℝ) / 12597 := by
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
    (completeRAData (tableEnvelope C) 12597 162).locationBound 12597 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12597 162).energyBound 12597 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12597 162) (d.f1 12597 162) d.f2 ≤
      32 * (((4676961483 / 1000000000000000000) : ℝ) + (780156721 / 500000000000000000) + (120007 / 320000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12597 162) (d.w1 12597 162)
      (d.w2 12597 162) ≤
      32 * (((1878538403 / 100000000000000000000) : ℝ) + (334136033 / 25000000000000000000) + (48833977 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12597 162) (d.f1 12597 162) d.f2 ≤
      ((4676961483 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4676961483 / 1000000000000000000)) * ((780156721 / 500000000000000000)) * (126 / 100) +
      2 * (((780156721 / 500000000000000000)) ^ 2 + 2 * ((4676961483 / 1000000000000000000)) * ((120007 / 320000000000000))) +
      6 * ((780156721 / 500000000000000000)) * ((120007 / 320000000000000)) * (126 / 100) + 8 * ((120007 / 320000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12597 162) (d.f1 12597 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12597 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12597 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12597 162) (d.f1 12597 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12597 162) (d.w1 12597 162) (d.w2 12597 162)
  have hwexpr0 : 0 ≤ d.w0 12597 162 + d.w1 12597 162 * √(π / 2) +
      2 * d.w2 12597 162 + energyR16 12597 *
      radiusPolynomialRoot16 (d.w0 12597 162) (d.w1 12597 162) (d.w2 12597 162) := by
    positivity
  constructor
  · change (12597 : ℝ) ^ 8 * (mA 12597 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12597 162) (d.f1 12597 162) d.f2 + locationR16 12597 *
        radiusPolynomialRoot16 (d.f0 12597 162) (d.f1 12597 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12597 : ℝ) ^ 8 * (mA 12597 : ℝ) ^ 8 *
        ((((4676961483 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4676961483 / 1000000000000000000)) * ((780156721 / 500000000000000000)) * (126 / 100) +
          2 * (((780156721 / 500000000000000000)) ^ 2 + 2 * ((4676961483 / 1000000000000000000)) * ((120007 / 320000000000000))) +
          6 * ((780156721 / 500000000000000000)) * ((120007 / 320000000000000)) * (126 / 100) + 8 * ((120007 / 320000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12597) *
          (32 * (((4676961483 / 1000000000000000000) : ℝ) + (780156721 / 500000000000000000) + (120007 / 320000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12597 : ℝ) ^ 16 *
      (d.w0 12597 162 + d.w1 12597 162 * √(π / 2) + 2 * d.w2 12597 162 +
        energyR16 12597 * radiusPolynomialRoot16 (d.w0 12597 162) (d.w1 12597 162)
          (d.w2 12597 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12597 : ℝ) ^ 16 *
        (((1878538403 / 100000000000000000000) : ℝ) + ((334136033 / 25000000000000000000)) * (126 / 100) + 2 * ((48833977 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12597) *
          (32 * (((1878538403 / 100000000000000000000) : ℝ) + (334136033 / 25000000000000000000) + (48833977 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12597

/-! A coarse bound on the actual paper statistics constant at dimension 12598. -/
namespace BstLean.Part266.Row12598
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12596 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12596 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12596 128 ≤ (12850 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12850 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12598) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12598 : ℕ))
    (by norm_num : (12598 : ℕ) ≤ 16384)
  have ht : paperTail256 12598 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12598 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12598 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12598 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12598 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12598 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12596 128 * √(2 / (12598 : ℝ)) *
      (√(12598 : ℝ) + paperT0 12598 + paperTail256 12598) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12598 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12598 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12598 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12596 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12596 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12598 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12598

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12598
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12598 (61 / 100) 162 (17 / (100 * 12598)) (26 / (10 * 12598)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12598 (61 / 100) 162 (17 / (100 * 12598)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (30513637 / 6250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (15501451 / 10000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2729676219 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12598 / 12598 * (61 / 100)) ^ 4 * inverseRadius8 (12598 - 1) /
            envelopeGap 12598 (61 / 100) 162 (17 / (100 * 12598)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12598

namespace BstLean.Part266.Row12598
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12598 162 ≤ (935206817 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12598 162 ≤ (1560003971 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (187473737 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12598 162 ≤ (93904561 / 5000000000000000000)
  w1 : (tableEnvelope C).w1 12598 162 ≤ (267245187 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12598 162 ≤ (488223481 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (30513637 / 6250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (30513637 / 6250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (15501451 / 10000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2729676219 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((734689 / 200000000) : ℝ) ≤ √(17 / (100 * 12598) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12598) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2209566003 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39371882099 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12598) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12598) ≤ (112256991 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12598) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12598 * (162 : ℝ) ^ 2 + 26 / (10 * 12598) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12598) : ℝ)) (tA 12598 * 162 ^ 2 + 26 / (10 * 12598)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((734689 / 200000000))) * ((30513637 / 6250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((734689 / 200000000)) ^ 3) * ((15501451 / 10000000000000000000000))) + ((2729676219 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((734689 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12598) : ℝ)) d.D d.V d.P (√(tA 12598) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((734689 / 200000000)) ^ 2 * (((2209566003 / 1000000000000000)) * ((39371882099 / 1000000000000000000)))) + ((2729676219 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12598) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((734689 / 200000000)) * ((30513637 / 6250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12598) : ℝ)) (tA 12598 * 162 ^ 2 + 26 / (10 * 12598)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((30513637 / 6250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((734689 / 200000000)) ^ 2) * ((15501451 / 10000000000000000000000)) + ((2729676219 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12598) : ℝ)) (√(26 / (10 * 12598) : ℝ)) d.D d.V d.P (√(tA 12598) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((734689 / 200000000)) * (((2209566003 / 1000000000000000)) * ((39371882099 / 1000000000000000000))) + ((2729676219 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12598) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((30513637 / 6250000000000000000) : ℝ) + ((2729676219 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12598

namespace BstLean.Part266.Row12598
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12598 162 ∧
    0 ≤ (tableEnvelope C).f1 12598 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12598 162 ∧
    0 ≤ (tableEnvelope C).w1 12598 162 ∧ 0 ≤ (tableEnvelope C).w2 12598 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12598 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12598 162 ∧ 0 ≤ d.f1 12598 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12598 162 ∧ 0 ≤ d.w1 12598 162 ∧ 0 ≤ d.w2 12598 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12598 ≤ 2 * (228 / 100 : ℝ) / 12598 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12598 ≤ 2 * (370 / 100 : ℝ) / 12598 := by
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
    (completeRAData (tableEnvelope C) 12598 162).locationBound 12598 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12598 162).energyBound 12598 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12598 162) (d.f1 12598 162) d.f2 ≤
      32 * (((935206817 / 200000000000000000) : ℝ) + (1560003971 / 1000000000000000000) + (187473737 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12598 162) (d.w1 12598 162)
      (d.w2 12598 162) ≤
      32 * (((93904561 / 5000000000000000000) : ℝ) + (267245187 / 20000000000000000000) + (488223481 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12598 162) (d.f1 12598 162) d.f2 ≤
      ((935206817 / 200000000000000000) : ℝ) ^ 2 + 2 * ((935206817 / 200000000000000000)) * ((1560003971 / 1000000000000000000)) * (126 / 100) +
      2 * (((1560003971 / 1000000000000000000)) ^ 2 + 2 * ((935206817 / 200000000000000000)) * ((187473737 / 500000000000000000))) +
      6 * ((1560003971 / 1000000000000000000)) * ((187473737 / 500000000000000000)) * (126 / 100) + 8 * ((187473737 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12598 162) (d.f1 12598 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12598 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12598 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12598 162) (d.f1 12598 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12598 162) (d.w1 12598 162) (d.w2 12598 162)
  have hwexpr0 : 0 ≤ d.w0 12598 162 + d.w1 12598 162 * √(π / 2) +
      2 * d.w2 12598 162 + energyR16 12598 *
      radiusPolynomialRoot16 (d.w0 12598 162) (d.w1 12598 162) (d.w2 12598 162) := by
    positivity
  constructor
  · change (12598 : ℝ) ^ 8 * (mA 12598 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12598 162) (d.f1 12598 162) d.f2 + locationR16 12598 *
        radiusPolynomialRoot16 (d.f0 12598 162) (d.f1 12598 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12598 : ℝ) ^ 8 * (mA 12598 : ℝ) ^ 8 *
        ((((935206817 / 200000000000000000) : ℝ) ^ 2 + 2 * ((935206817 / 200000000000000000)) * ((1560003971 / 1000000000000000000)) * (126 / 100) +
          2 * (((1560003971 / 1000000000000000000)) ^ 2 + 2 * ((935206817 / 200000000000000000)) * ((187473737 / 500000000000000000))) +
          6 * ((1560003971 / 1000000000000000000)) * ((187473737 / 500000000000000000)) * (126 / 100) + 8 * ((187473737 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12598) *
          (32 * (((935206817 / 200000000000000000) : ℝ) + (1560003971 / 1000000000000000000) + (187473737 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12598 : ℝ) ^ 16 *
      (d.w0 12598 162 + d.w1 12598 162 * √(π / 2) + 2 * d.w2 12598 162 +
        energyR16 12598 * radiusPolynomialRoot16 (d.w0 12598 162) (d.w1 12598 162)
          (d.w2 12598 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12598 : ℝ) ^ 16 *
        (((93904561 / 5000000000000000000) : ℝ) + ((267245187 / 20000000000000000000)) * (126 / 100) + 2 * ((488223481 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12598) *
          (32 * (((93904561 / 5000000000000000000) : ℝ) + (267245187 / 20000000000000000000) + (488223481 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12598

/-! A coarse bound on the actual paper statistics constant at dimension 12599. -/
namespace BstLean.Part266.Row12599
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12597 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12597 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12597 128 ≤ (12851 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12851 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12599) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12599 : ℕ))
    (by norm_num : (12599 : ℕ) ≤ 16384)
  have ht : paperTail256 12599 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12599 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12599 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12599 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12599 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12599 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12597 128 * √(2 / (12599 : ℝ)) *
      (√(12599 : ℝ) + paperT0 12599 + paperTail256 12599) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12599 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12599 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12599 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12597 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12597 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12599 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12599

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12599
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12599 (61 / 100) 162 (17 / (100 * 12599)) (26 / (10 * 12599)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12599 (61 / 100) 162 (17 / (100 * 12599)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (488101943 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (154965299 / 100000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5455852993 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12599 / 12599 * (61 / 100)) ^ 4 * inverseRadius8 (12599 - 1) /
            envelopeGap 12599 (61 / 100) 162 (17 / (100 * 12599)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12599

namespace BstLean.Part266.Row12599
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12599 162 ≤ (2337551667 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12599 162 ≤ (194961719 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (374872993 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12599 162 ≤ (469410859 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12599 162 ≤ (667953741 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12599 162 ≤ (488107229 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (488101943 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (488101943 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (154965299 / 100000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5455852993 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((36733 / 10000000) : ℝ) ≤ √(17 / (100 * 12599) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12599) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2209302929 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9841408023 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12599) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12599) ≤ (112248081 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12599) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12599 * (162 : ℝ) ^ 2 + 26 / (10 * 12599) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12599) : ℝ)) (tA 12599 * 162 ^ 2 + 26 / (10 * 12599)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((36733 / 10000000))) * ((488101943 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((36733 / 10000000)) ^ 3) * ((154965299 / 100000000000000000000000))) + ((5455852993 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((36733 / 10000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12599) : ℝ)) d.D d.V d.P (√(tA 12599) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((36733 / 10000000)) ^ 2 * (((2209302929 / 1000000000000000)) * ((9841408023 / 250000000000000000)))) + ((5455852993 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12599) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((36733 / 10000000)) * ((488101943 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12599) : ℝ)) (tA 12599 * 162 ^ 2 + 26 / (10 * 12599)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((488101943 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((36733 / 10000000)) ^ 2) * ((154965299 / 100000000000000000000000)) + ((5455852993 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12599) : ℝ)) (√(26 / (10 * 12599) : ℝ)) d.D d.V d.P (√(tA 12599) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((36733 / 10000000)) * (((2209302929 / 1000000000000000)) * ((9841408023 / 250000000000000000))) + ((5455852993 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12599) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((488101943 / 100000000000000000000) : ℝ) + ((5455852993 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12599

namespace BstLean.Part266.Row12599
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12599 162 ∧
    0 ≤ (tableEnvelope C).f1 12599 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12599 162 ∧
    0 ≤ (tableEnvelope C).w1 12599 162 ∧ 0 ≤ (tableEnvelope C).w2 12599 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12599 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12599 162 ∧ 0 ≤ d.f1 12599 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12599 162 ∧ 0 ≤ d.w1 12599 162 ∧ 0 ≤ d.w2 12599 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12599 ≤ 2 * (228 / 100 : ℝ) / 12599 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12599 ≤ 2 * (370 / 100 : ℝ) / 12599 := by
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
    (completeRAData (tableEnvelope C) 12599 162).locationBound 12599 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12599 162).energyBound 12599 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12599 162) (d.f1 12599 162) d.f2 ≤
      32 * (((2337551667 / 500000000000000000) : ℝ) + (194961719 / 125000000000000000) + (374872993 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12599 162) (d.w1 12599 162)
      (d.w2 12599 162) ≤
      32 * (((469410859 / 25000000000000000000) : ℝ) + (667953741 / 50000000000000000000) + (488107229 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12599 162) (d.f1 12599 162) d.f2 ≤
      ((2337551667 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2337551667 / 500000000000000000)) * ((194961719 / 125000000000000000)) * (126 / 100) +
      2 * (((194961719 / 125000000000000000)) ^ 2 + 2 * ((2337551667 / 500000000000000000)) * ((374872993 / 1000000000000000000))) +
      6 * ((194961719 / 125000000000000000)) * ((374872993 / 1000000000000000000)) * (126 / 100) + 8 * ((374872993 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12599 162) (d.f1 12599 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12599 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12599 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12599 162) (d.f1 12599 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12599 162) (d.w1 12599 162) (d.w2 12599 162)
  have hwexpr0 : 0 ≤ d.w0 12599 162 + d.w1 12599 162 * √(π / 2) +
      2 * d.w2 12599 162 + energyR16 12599 *
      radiusPolynomialRoot16 (d.w0 12599 162) (d.w1 12599 162) (d.w2 12599 162) := by
    positivity
  constructor
  · change (12599 : ℝ) ^ 8 * (mA 12599 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12599 162) (d.f1 12599 162) d.f2 + locationR16 12599 *
        radiusPolynomialRoot16 (d.f0 12599 162) (d.f1 12599 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12599 : ℝ) ^ 8 * (mA 12599 : ℝ) ^ 8 *
        ((((2337551667 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2337551667 / 500000000000000000)) * ((194961719 / 125000000000000000)) * (126 / 100) +
          2 * (((194961719 / 125000000000000000)) ^ 2 + 2 * ((2337551667 / 500000000000000000)) * ((374872993 / 1000000000000000000))) +
          6 * ((194961719 / 125000000000000000)) * ((374872993 / 1000000000000000000)) * (126 / 100) + 8 * ((374872993 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12599) *
          (32 * (((2337551667 / 500000000000000000) : ℝ) + (194961719 / 125000000000000000) + (374872993 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12599 : ℝ) ^ 16 *
      (d.w0 12599 162 + d.w1 12599 162 * √(π / 2) + 2 * d.w2 12599 162 +
        energyR16 12599 * radiusPolynomialRoot16 (d.w0 12599 162) (d.w1 12599 162)
          (d.w2 12599 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12599 : ℝ) ^ 16 *
        (((469410859 / 25000000000000000000) : ℝ) + ((667953741 / 50000000000000000000)) * (126 / 100) + 2 * ((488107229 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12599) *
          (32 * (((469410859 / 25000000000000000000) : ℝ) + (667953741 / 50000000000000000000) + (488107229 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12599
