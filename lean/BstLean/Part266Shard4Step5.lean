import BstLean.Part266Shard4Step4


/-! A coarse bound on the actual paper statistics constant at dimension 12450. -/
namespace BstLean.Part266.Row12450
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12448 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12448 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12448 128 ≤ (12702 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12702 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12450) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12450 : ℕ))
    (by norm_num : (12450 : ℕ) ≤ 16384)
  have ht : paperTail256 12450 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12450 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12450 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12450 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12450 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12450 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12448 128 * √(2 / (12450 : ℝ)) *
      (√(12450 : ℝ) + paperT0 12450 + paperTail256 12450) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12450 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12450 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12450 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12448 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12448 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12450 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12450

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12450
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12450 (61 / 100) 161 (17 / (100 * 12450)) (26 / (10 * 12450)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12450 (61 / 100) 161 (17 / (100 * 12450)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (252919049 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (406295667 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (750423733 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12450 / 12450 * (61 / 100)) ^ 4 * inverseRadius8 (12450 - 1) /
            envelopeGap 12450 (61 / 100) 161 (17 / (100 * 12450)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12450

namespace BstLean.Part266.Row12450
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12450 161 ≤ (4816249703 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12450 161 ≤ (401695611 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (15447629 / 40000000000000000)
  w0 : (tableEnvelope C).w0 12450 161 ≤ (1945871747 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12450 161 ≤ (692225273 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12450 161 ≤ (252921957 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (252919049 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (252919049 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (406295667 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (750423733 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((739043 / 200000000) : ℝ) ≤ √(17 / (100 * 12450) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12450) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (562271119 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (10078388599 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12450) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12450) ≤ (113591451 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12450) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12450 * (161 : ℝ) ^ 2 + 26 / (10 * 12450) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12450) : ℝ)) (tA 12450 * 161 ^ 2 + 26 / (10 * 12450)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((739043 / 200000000))) * ((252919049 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((739043 / 200000000)) ^ 3) * ((406295667 / 250000000000000000000000))) + ((750423733 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((739043 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12450) : ℝ)) d.D d.V d.P (√(tA 12450) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((739043 / 200000000)) ^ 2 * (((562271119 / 250000000000000)) * ((10078388599 / 250000000000000000)))) + ((750423733 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12450) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((739043 / 200000000)) * ((252919049 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12450) : ℝ)) (tA 12450 * 161 ^ 2 + 26 / (10 * 12450)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((252919049 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((739043 / 200000000)) ^ 2) * ((406295667 / 250000000000000000000000)) + ((750423733 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12450) : ℝ)) (√(26 / (10 * 12450) : ℝ)) d.D d.V d.P (√(tA 12450) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((739043 / 200000000)) * (((562271119 / 250000000000000)) * ((10078388599 / 250000000000000000))) + ((750423733 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12450) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((252919049 / 50000000000000000000) : ℝ) + ((750423733 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12450

namespace BstLean.Part266.Row12450
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12450 161 ∧
    0 ≤ (tableEnvelope C).f1 12450 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12450 161 ∧
    0 ≤ (tableEnvelope C).w1 12450 161 ∧ 0 ≤ (tableEnvelope C).w2 12450 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12450 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12450 161 ∧ 0 ≤ d.f1 12450 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12450 161 ∧ 0 ≤ d.w1 12450 161 ∧ 0 ≤ d.w2 12450 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12450 ≤ 2 * (228 / 100 : ℝ) / 12450 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12450 ≤ 2 * (370 / 100 : ℝ) / 12450 := by
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
    (completeRAData (tableEnvelope C) 12450 161).locationBound 12450 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12450 161).energyBound 12450 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12450 161) (d.f1 12450 161) d.f2 ≤
      32 * (((4816249703 / 1000000000000000000) : ℝ) + (401695611 / 250000000000000000) + (15447629 / 40000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12450 161) (d.w1 12450 161)
      (d.w2 12450 161) ≤
      32 * (((1945871747 / 100000000000000000000) : ℝ) + (692225273 / 50000000000000000000) + (252921957 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12450 161) (d.f1 12450 161) d.f2 ≤
      ((4816249703 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4816249703 / 1000000000000000000)) * ((401695611 / 250000000000000000)) * (126 / 100) +
      2 * (((401695611 / 250000000000000000)) ^ 2 + 2 * ((4816249703 / 1000000000000000000)) * ((15447629 / 40000000000000000))) +
      6 * ((401695611 / 250000000000000000)) * ((15447629 / 40000000000000000)) * (126 / 100) + 8 * ((15447629 / 40000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12450 161) (d.f1 12450 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12450 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12450 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12450 161) (d.f1 12450 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12450 161) (d.w1 12450 161) (d.w2 12450 161)
  have hwexpr0 : 0 ≤ d.w0 12450 161 + d.w1 12450 161 * √(π / 2) +
      2 * d.w2 12450 161 + energyR16 12450 *
      radiusPolynomialRoot16 (d.w0 12450 161) (d.w1 12450 161) (d.w2 12450 161) := by
    positivity
  constructor
  · change (12450 : ℝ) ^ 8 * (mA 12450 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12450 161) (d.f1 12450 161) d.f2 + locationR16 12450 *
        radiusPolynomialRoot16 (d.f0 12450 161) (d.f1 12450 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12450 : ℝ) ^ 8 * (mA 12450 : ℝ) ^ 8 *
        ((((4816249703 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4816249703 / 1000000000000000000)) * ((401695611 / 250000000000000000)) * (126 / 100) +
          2 * (((401695611 / 250000000000000000)) ^ 2 + 2 * ((4816249703 / 1000000000000000000)) * ((15447629 / 40000000000000000))) +
          6 * ((401695611 / 250000000000000000)) * ((15447629 / 40000000000000000)) * (126 / 100) + 8 * ((15447629 / 40000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12450) *
          (32 * (((4816249703 / 1000000000000000000) : ℝ) + (401695611 / 250000000000000000) + (15447629 / 40000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12450 : ℝ) ^ 16 *
      (d.w0 12450 161 + d.w1 12450 161 * √(π / 2) + 2 * d.w2 12450 161 +
        energyR16 12450 * radiusPolynomialRoot16 (d.w0 12450 161) (d.w1 12450 161)
          (d.w2 12450 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12450 : ℝ) ^ 16 *
        (((1945871747 / 100000000000000000000) : ℝ) + ((692225273 / 50000000000000000000)) * (126 / 100) + 2 * ((252921957 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12450) *
          (32 * (((1945871747 / 100000000000000000000) : ℝ) + (692225273 / 50000000000000000000) + (252921957 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12450

/-! A coarse bound on the actual paper statistics constant at dimension 12451. -/
namespace BstLean.Part266.Row12451
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12449 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12449 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12449 128 ≤ (12703 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12703 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12451) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12451 : ℕ))
    (by norm_num : (12451 : ℕ) ≤ 16384)
  have ht : paperTail256 12451 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12451 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12451 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12451 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12451 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12451 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12449 128 * √(2 / (12451 : ℝ)) *
      (√(12451 : ℝ) + paperT0 12451 + paperTail256 12451) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12451 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12451 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12451 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12449 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12449 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12451 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12451

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12451
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12451 (61 / 100) 161 (17 / (100 * 12451)) (26 / (10 * 12451)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12451 (61 / 100) 161 (17 / (100 * 12451)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (252858111 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (324932121 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5999495533 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12451 / 12451 * (61 / 100)) ^ 4 * inverseRadius8 (12451 - 1) /
            envelopeGap 12451 (61 / 100) 161 (17 / (100 * 12451)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12451

namespace BstLean.Part266.Row12451
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12451 161 ≤ (240764059 / 50000000000000000)
  f1 : (tableEnvelope C).f1 12451 161 ≤ (1606459479 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (386113141 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12451 161 ≤ (389080521 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12451 161 ≤ (43253651 / 3125000000000000000)
  w2 : (tableEnvelope C).w2 12451 161 ≤ (252861017 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (252858111 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (252858111 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (324932121 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5999495533 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3695067 / 1000000000) : ℝ) ≤ √(17 / (100 * 12451) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12451) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1124406757 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (8061415769 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12451) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12451) ≤ (14197791 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12451) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12451 * (161 : ℝ) ^ 2 + 26 / (10 * 12451) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12451) : ℝ)) (tA 12451 * 161 ^ 2 + 26 / (10 * 12451)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3695067 / 1000000000))) * ((252858111 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3695067 / 1000000000)) ^ 3) * ((324932121 / 200000000000000000000000))) + ((5999495533 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3695067 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12451) : ℝ)) d.D d.V d.P (√(tA 12451) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3695067 / 1000000000)) ^ 2 * (((1124406757 / 500000000000000)) * ((8061415769 / 200000000000000000)))) + ((5999495533 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12451) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3695067 / 1000000000)) * ((252858111 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12451) : ℝ)) (tA 12451 * 161 ^ 2 + 26 / (10 * 12451)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((252858111 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3695067 / 1000000000)) ^ 2) * ((324932121 / 200000000000000000000000)) + ((5999495533 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12451) : ℝ)) (√(26 / (10 * 12451) : ℝ)) d.D d.V d.P (√(tA 12451) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3695067 / 1000000000)) * (((1124406757 / 500000000000000)) * ((8061415769 / 200000000000000000))) + ((5999495533 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12451) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((252858111 / 50000000000000000000) : ℝ) + ((5999495533 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12451

namespace BstLean.Part266.Row12451
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12451 161 ∧
    0 ≤ (tableEnvelope C).f1 12451 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12451 161 ∧
    0 ≤ (tableEnvelope C).w1 12451 161 ∧ 0 ≤ (tableEnvelope C).w2 12451 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12451 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12451 161 ∧ 0 ≤ d.f1 12451 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12451 161 ∧ 0 ≤ d.w1 12451 161 ∧ 0 ≤ d.w2 12451 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12451 ≤ 2 * (228 / 100 : ℝ) / 12451 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12451 ≤ 2 * (370 / 100 : ℝ) / 12451 := by
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
    (completeRAData (tableEnvelope C) 12451 161).locationBound 12451 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12451 161).energyBound 12451 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12451 161) (d.f1 12451 161) d.f2 ≤
      32 * (((240764059 / 50000000000000000) : ℝ) + (1606459479 / 1000000000000000000) + (386113141 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12451 161) (d.w1 12451 161)
      (d.w2 12451 161) ≤
      32 * (((389080521 / 20000000000000000000) : ℝ) + (43253651 / 3125000000000000000) + (252861017 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12451 161) (d.f1 12451 161) d.f2 ≤
      ((240764059 / 50000000000000000) : ℝ) ^ 2 + 2 * ((240764059 / 50000000000000000)) * ((1606459479 / 1000000000000000000)) * (126 / 100) +
      2 * (((1606459479 / 1000000000000000000)) ^ 2 + 2 * ((240764059 / 50000000000000000)) * ((386113141 / 1000000000000000000))) +
      6 * ((1606459479 / 1000000000000000000)) * ((386113141 / 1000000000000000000)) * (126 / 100) + 8 * ((386113141 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12451 161) (d.f1 12451 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12451 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12451 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12451 161) (d.f1 12451 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12451 161) (d.w1 12451 161) (d.w2 12451 161)
  have hwexpr0 : 0 ≤ d.w0 12451 161 + d.w1 12451 161 * √(π / 2) +
      2 * d.w2 12451 161 + energyR16 12451 *
      radiusPolynomialRoot16 (d.w0 12451 161) (d.w1 12451 161) (d.w2 12451 161) := by
    positivity
  constructor
  · change (12451 : ℝ) ^ 8 * (mA 12451 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12451 161) (d.f1 12451 161) d.f2 + locationR16 12451 *
        radiusPolynomialRoot16 (d.f0 12451 161) (d.f1 12451 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12451 : ℝ) ^ 8 * (mA 12451 : ℝ) ^ 8 *
        ((((240764059 / 50000000000000000) : ℝ) ^ 2 + 2 * ((240764059 / 50000000000000000)) * ((1606459479 / 1000000000000000000)) * (126 / 100) +
          2 * (((1606459479 / 1000000000000000000)) ^ 2 + 2 * ((240764059 / 50000000000000000)) * ((386113141 / 1000000000000000000))) +
          6 * ((1606459479 / 1000000000000000000)) * ((386113141 / 1000000000000000000)) * (126 / 100) + 8 * ((386113141 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12451) *
          (32 * (((240764059 / 50000000000000000) : ℝ) + (1606459479 / 1000000000000000000) + (386113141 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12451 : ℝ) ^ 16 *
      (d.w0 12451 161 + d.w1 12451 161 * √(π / 2) + 2 * d.w2 12451 161 +
        energyR16 12451 * radiusPolynomialRoot16 (d.w0 12451 161) (d.w1 12451 161)
          (d.w2 12451 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12451 : ℝ) ^ 16 *
        (((389080521 / 20000000000000000000) : ℝ) + ((43253651 / 3125000000000000000)) * (126 / 100) + 2 * ((252861017 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12451) *
          (32 * (((389080521 / 20000000000000000000) : ℝ) + (43253651 / 3125000000000000000) + (252861017 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12451

/-! A coarse bound on the actual paper statistics constant at dimension 12452. -/
namespace BstLean.Part266.Row12452
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12450 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12450 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12450 128 ≤ (12704 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12704 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12452) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12452 : ℕ))
    (by norm_num : (12452 : ℕ) ≤ 16384)
  have ht : paperTail256 12452 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12452 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12452 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12452 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12452 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12452 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12450 128 * √(2 / (12452 : ℝ)) *
      (√(12452 : ℝ) + paperT0 12452 + paperTail256 12452) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12452 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12452 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12452 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12450 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12450 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12452 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12452

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12452
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12452 (61 / 100) 161 (17 / (100 * 12452)) (26 / (10 * 12452)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12452 (61 / 100) 161 (17 / (100 * 12452)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (252797193 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1624138751 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5995604047 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12452 / 12452 * (61 / 100)) ^ 4 * inverseRadius8 (12452 - 1) /
            envelopeGap 12452 (61 / 100) 161 (17 / (100 * 12452)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12452

namespace BstLean.Part266.Row12452
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12452 161 ≤ (962863351 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12452 161 ≤ (1606137491 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (193017843 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12452 161 ≤ (1944934407 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12452 161 ≤ (691891803 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12452 161 ≤ (252800097 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (252797193 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (252797193 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1624138751 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5995604047 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1847459 / 500000000) : ℝ) ≤ √(17 / (100 * 12452) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12452) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2248542609 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40300604847 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12452) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12452) ≤ (113573207 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12452) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12452 * (161 : ℝ) ^ 2 + 26 / (10 * 12452) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12452) : ℝ)) (tA 12452 * 161 ^ 2 + 26 / (10 * 12452)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1847459 / 500000000))) * ((252797193 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1847459 / 500000000)) ^ 3) * ((1624138751 / 1000000000000000000000000))) + ((5995604047 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1847459 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12452) : ℝ)) d.D d.V d.P (√(tA 12452) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1847459 / 500000000)) ^ 2 * (((2248542609 / 1000000000000000)) * ((40300604847 / 1000000000000000000)))) + ((5995604047 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12452) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1847459 / 500000000)) * ((252797193 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12452) : ℝ)) (tA 12452 * 161 ^ 2 + 26 / (10 * 12452)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((252797193 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1847459 / 500000000)) ^ 2) * ((1624138751 / 1000000000000000000000000)) + ((5995604047 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12452) : ℝ)) (√(26 / (10 * 12452) : ℝ)) d.D d.V d.P (√(tA 12452) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1847459 / 500000000)) * (((2248542609 / 1000000000000000)) * ((40300604847 / 1000000000000000000))) + ((5995604047 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12452) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((252797193 / 50000000000000000000) : ℝ) + ((5995604047 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12452

namespace BstLean.Part266.Row12452
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12452 161 ∧
    0 ≤ (tableEnvelope C).f1 12452 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12452 161 ∧
    0 ≤ (tableEnvelope C).w1 12452 161 ∧ 0 ≤ (tableEnvelope C).w2 12452 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12452 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12452 161 ∧ 0 ≤ d.f1 12452 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12452 161 ∧ 0 ≤ d.w1 12452 161 ∧ 0 ≤ d.w2 12452 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12452 ≤ 2 * (228 / 100 : ℝ) / 12452 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12452 ≤ 2 * (370 / 100 : ℝ) / 12452 := by
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
    (completeRAData (tableEnvelope C) 12452 161).locationBound 12452 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12452 161).energyBound 12452 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12452 161) (d.f1 12452 161) d.f2 ≤
      32 * (((962863351 / 200000000000000000) : ℝ) + (1606137491 / 1000000000000000000) + (193017843 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12452 161) (d.w1 12452 161)
      (d.w2 12452 161) ≤
      32 * (((1944934407 / 100000000000000000000) : ℝ) + (691891803 / 50000000000000000000) + (252800097 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12452 161) (d.f1 12452 161) d.f2 ≤
      ((962863351 / 200000000000000000) : ℝ) ^ 2 + 2 * ((962863351 / 200000000000000000)) * ((1606137491 / 1000000000000000000)) * (126 / 100) +
      2 * (((1606137491 / 1000000000000000000)) ^ 2 + 2 * ((962863351 / 200000000000000000)) * ((193017843 / 500000000000000000))) +
      6 * ((1606137491 / 1000000000000000000)) * ((193017843 / 500000000000000000)) * (126 / 100) + 8 * ((193017843 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12452 161) (d.f1 12452 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12452 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12452 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12452 161) (d.f1 12452 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12452 161) (d.w1 12452 161) (d.w2 12452 161)
  have hwexpr0 : 0 ≤ d.w0 12452 161 + d.w1 12452 161 * √(π / 2) +
      2 * d.w2 12452 161 + energyR16 12452 *
      radiusPolynomialRoot16 (d.w0 12452 161) (d.w1 12452 161) (d.w2 12452 161) := by
    positivity
  constructor
  · change (12452 : ℝ) ^ 8 * (mA 12452 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12452 161) (d.f1 12452 161) d.f2 + locationR16 12452 *
        radiusPolynomialRoot16 (d.f0 12452 161) (d.f1 12452 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12452 : ℝ) ^ 8 * (mA 12452 : ℝ) ^ 8 *
        ((((962863351 / 200000000000000000) : ℝ) ^ 2 + 2 * ((962863351 / 200000000000000000)) * ((1606137491 / 1000000000000000000)) * (126 / 100) +
          2 * (((1606137491 / 1000000000000000000)) ^ 2 + 2 * ((962863351 / 200000000000000000)) * ((193017843 / 500000000000000000))) +
          6 * ((1606137491 / 1000000000000000000)) * ((193017843 / 500000000000000000)) * (126 / 100) + 8 * ((193017843 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12452) *
          (32 * (((962863351 / 200000000000000000) : ℝ) + (1606137491 / 1000000000000000000) + (193017843 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12452 : ℝ) ^ 16 *
      (d.w0 12452 161 + d.w1 12452 161 * √(π / 2) + 2 * d.w2 12452 161 +
        energyR16 12452 * radiusPolynomialRoot16 (d.w0 12452 161) (d.w1 12452 161)
          (d.w2 12452 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12452 : ℝ) ^ 16 *
        (((1944934407 / 100000000000000000000) : ℝ) + ((691891803 / 50000000000000000000)) * (126 / 100) + 2 * ((252800097 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12452) *
          (32 * (((1944934407 / 100000000000000000000) : ℝ) + (691891803 / 50000000000000000000) + (252800097 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12452

/-! A coarse bound on the actual paper statistics constant at dimension 12453. -/
namespace BstLean.Part266.Row12453
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12451 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12451 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12451 128 ≤ (12705 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12705 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12453) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12453 : ℕ))
    (by norm_num : (12453 : ℕ) ≤ 16384)
  have ht : paperTail256 12453 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12453 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12453 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12453 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12453 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12453 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12451 128 * √(2 / (12453 : ℝ)) *
      (√(12453 : ℝ) + paperT0 12453 + paperTail256 12453) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12453 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12453 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12453 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12451 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12451 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12453 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12453

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12453
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12453 (61 / 100) 161 (17 / (100 * 12453)) (26 / (10 * 12453)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12453 (61 / 100) 161 (17 / (100 * 12453)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (126368147 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1623617107 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5991715403 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12453 / 12453 * (61 / 100)) ^ 4 * inverseRadius8 (12453 - 1) /
            envelopeGap 12453 (61 / 100) 161 (17 / (100 * 12453)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12453

namespace BstLean.Part266.Row12453
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12453 161 ≤ (4813348909 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12453 161 ≤ (802907369 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (7719163 / 20000000000000000)
  w0 : (tableEnvelope C).w0 12453 161 ≤ (972232797 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12453 161 ≤ (1383450119 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12453 161 ≤ (505478393 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (126368147 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (126368147 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1623617107 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5991715403 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((369477 / 100000000) : ℝ) ≤ √(17 / (100 * 12453) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12453) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (449654351 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (8058826483 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12453) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12453) ≤ (56782043 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12453) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12453 * (161 : ℝ) ^ 2 + 26 / (10 * 12453) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12453) : ℝ)) (tA 12453 * 161 ^ 2 + 26 / (10 * 12453)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((369477 / 100000000))) * ((126368147 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((369477 / 100000000)) ^ 3) * ((1623617107 / 1000000000000000000000000))) + ((5991715403 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((369477 / 100000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12453) : ℝ)) d.D d.V d.P (√(tA 12453) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((369477 / 100000000)) ^ 2 * (((449654351 / 200000000000000)) * ((8058826483 / 200000000000000000)))) + ((5991715403 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12453) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((369477 / 100000000)) * ((126368147 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12453) : ℝ)) (tA 12453 * 161 ^ 2 + 26 / (10 * 12453)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((126368147 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((369477 / 100000000)) ^ 2) * ((1623617107 / 1000000000000000000000000)) + ((5991715403 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12453) : ℝ)) (√(26 / (10 * 12453) : ℝ)) d.D d.V d.P (√(tA 12453) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((369477 / 100000000)) * (((449654351 / 200000000000000)) * ((8058826483 / 200000000000000000))) + ((5991715403 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12453) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((126368147 / 25000000000000000000) : ℝ) + ((5991715403 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12453

namespace BstLean.Part266.Row12453
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12453 161 ∧
    0 ≤ (tableEnvelope C).f1 12453 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12453 161 ∧
    0 ≤ (tableEnvelope C).w1 12453 161 ∧ 0 ≤ (tableEnvelope C).w2 12453 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12453 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12453 161 ∧ 0 ≤ d.f1 12453 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12453 161 ∧ 0 ≤ d.w1 12453 161 ∧ 0 ≤ d.w2 12453 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12453 ≤ 2 * (228 / 100 : ℝ) / 12453 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12453 ≤ 2 * (370 / 100 : ℝ) / 12453 := by
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
    (completeRAData (tableEnvelope C) 12453 161).locationBound 12453 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12453 161).energyBound 12453 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12453 161) (d.f1 12453 161) d.f2 ≤
      32 * (((4813348909 / 1000000000000000000) : ℝ) + (802907369 / 500000000000000000) + (7719163 / 20000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12453 161) (d.w1 12453 161)
      (d.w2 12453 161) ≤
      32 * (((972232797 / 50000000000000000000) : ℝ) + (1383450119 / 100000000000000000000) + (505478393 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12453 161) (d.f1 12453 161) d.f2 ≤
      ((4813348909 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4813348909 / 1000000000000000000)) * ((802907369 / 500000000000000000)) * (126 / 100) +
      2 * (((802907369 / 500000000000000000)) ^ 2 + 2 * ((4813348909 / 1000000000000000000)) * ((7719163 / 20000000000000000))) +
      6 * ((802907369 / 500000000000000000)) * ((7719163 / 20000000000000000)) * (126 / 100) + 8 * ((7719163 / 20000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12453 161) (d.f1 12453 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12453 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12453 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12453 161) (d.f1 12453 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12453 161) (d.w1 12453 161) (d.w2 12453 161)
  have hwexpr0 : 0 ≤ d.w0 12453 161 + d.w1 12453 161 * √(π / 2) +
      2 * d.w2 12453 161 + energyR16 12453 *
      radiusPolynomialRoot16 (d.w0 12453 161) (d.w1 12453 161) (d.w2 12453 161) := by
    positivity
  constructor
  · change (12453 : ℝ) ^ 8 * (mA 12453 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12453 161) (d.f1 12453 161) d.f2 + locationR16 12453 *
        radiusPolynomialRoot16 (d.f0 12453 161) (d.f1 12453 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12453 : ℝ) ^ 8 * (mA 12453 : ℝ) ^ 8 *
        ((((4813348909 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4813348909 / 1000000000000000000)) * ((802907369 / 500000000000000000)) * (126 / 100) +
          2 * (((802907369 / 500000000000000000)) ^ 2 + 2 * ((4813348909 / 1000000000000000000)) * ((7719163 / 20000000000000000))) +
          6 * ((802907369 / 500000000000000000)) * ((7719163 / 20000000000000000)) * (126 / 100) + 8 * ((7719163 / 20000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12453) *
          (32 * (((4813348909 / 1000000000000000000) : ℝ) + (802907369 / 500000000000000000) + (7719163 / 20000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12453 : ℝ) ^ 16 *
      (d.w0 12453 161 + d.w1 12453 161 * √(π / 2) + 2 * d.w2 12453 161 +
        energyR16 12453 * radiusPolynomialRoot16 (d.w0 12453 161) (d.w1 12453 161)
          (d.w2 12453 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12453 : ℝ) ^ 16 *
        (((972232797 / 50000000000000000000) : ℝ) + ((1383450119 / 100000000000000000000)) * (126 / 100) + 2 * ((505478393 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12453) *
          (32 * (((972232797 / 50000000000000000000) : ℝ) + (1383450119 / 100000000000000000000) + (505478393 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12453

/-! A coarse bound on the actual paper statistics constant at dimension 12454. -/
namespace BstLean.Part266.Row12454
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12452 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12452 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12452 128 ≤ (12706 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12706 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12454) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12454 : ℕ))
    (by norm_num : (12454 : ℕ) ≤ 16384)
  have ht : paperTail256 12454 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12454 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12454 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12454 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12454 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12454 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12452 128 * √(2 / (12454 : ℝ)) *
      (√(12454 : ℝ) + paperT0 12454 + paperTail256 12454) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12454 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12454 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12454 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12452 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12452 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12454 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12454

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12454
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12454 (61 / 100) 161 (17 / (100 * 12454)) (26 / (10 * 12454)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12454 (61 / 100) 161 (17 / (100 * 12454)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (50535083 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (202886959 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5987829599 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12454 / 12454 * (61 / 100)) ^ 4 * inverseRadius8 (12454 - 1) /
            envelopeGap 12454 (61 / 100) 161 (17 / (100 * 12454)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12454

namespace BstLean.Part266.Row12454
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12454 161 ≤ (4812381401 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12454 161 ≤ (401373023 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (385880637 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12454 161 ≤ (971998473 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12454 161 ≤ (691558373 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12454 161 ≤ (505356631 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (50535083 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (50535083 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (202886959 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5987829599 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1847311 / 500000000) : ℝ) ≤ √(17 / (100 * 12454) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12454) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2248000957 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1258989423 / 31250000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12454) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12454) ≤ (14194371 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12454) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12454 * (161 : ℝ) ^ 2 + 26 / (10 * 12454) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12454) : ℝ)) (tA 12454 * 161 ^ 2 + 26 / (10 * 12454)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1847311 / 500000000))) * ((50535083 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1847311 / 500000000)) ^ 3) * ((202886959 / 125000000000000000000000))) + ((5987829599 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1847311 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12454) : ℝ)) d.D d.V d.P (√(tA 12454) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1847311 / 500000000)) ^ 2 * (((2248000957 / 1000000000000000)) * ((1258989423 / 31250000000000000)))) + ((5987829599 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12454) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1847311 / 500000000)) * ((50535083 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12454) : ℝ)) (tA 12454 * 161 ^ 2 + 26 / (10 * 12454)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((50535083 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1847311 / 500000000)) ^ 2) * ((202886959 / 125000000000000000000000)) + ((5987829599 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12454) : ℝ)) (√(26 / (10 * 12454) : ℝ)) d.D d.V d.P (√(tA 12454) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1847311 / 500000000)) * (((2248000957 / 1000000000000000)) * ((1258989423 / 31250000000000000))) + ((5987829599 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12454) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((50535083 / 10000000000000000000) : ℝ) + ((5987829599 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12454

namespace BstLean.Part266.Row12454
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12454 161 ∧
    0 ≤ (tableEnvelope C).f1 12454 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12454 161 ∧
    0 ≤ (tableEnvelope C).w1 12454 161 ∧ 0 ≤ (tableEnvelope C).w2 12454 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12454 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12454 161 ∧ 0 ≤ d.f1 12454 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12454 161 ∧ 0 ≤ d.w1 12454 161 ∧ 0 ≤ d.w2 12454 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12454 ≤ 2 * (228 / 100 : ℝ) / 12454 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12454 ≤ 2 * (370 / 100 : ℝ) / 12454 := by
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
    (completeRAData (tableEnvelope C) 12454 161).locationBound 12454 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12454 161).energyBound 12454 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12454 161) (d.f1 12454 161) d.f2 ≤
      32 * (((4812381401 / 1000000000000000000) : ℝ) + (401373023 / 250000000000000000) + (385880637 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12454 161) (d.w1 12454 161)
      (d.w2 12454 161) ≤
      32 * (((971998473 / 50000000000000000000) : ℝ) + (691558373 / 50000000000000000000) + (505356631 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12454 161) (d.f1 12454 161) d.f2 ≤
      ((4812381401 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4812381401 / 1000000000000000000)) * ((401373023 / 250000000000000000)) * (126 / 100) +
      2 * (((401373023 / 250000000000000000)) ^ 2 + 2 * ((4812381401 / 1000000000000000000)) * ((385880637 / 1000000000000000000))) +
      6 * ((401373023 / 250000000000000000)) * ((385880637 / 1000000000000000000)) * (126 / 100) + 8 * ((385880637 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12454 161) (d.f1 12454 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12454 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12454 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12454 161) (d.f1 12454 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12454 161) (d.w1 12454 161) (d.w2 12454 161)
  have hwexpr0 : 0 ≤ d.w0 12454 161 + d.w1 12454 161 * √(π / 2) +
      2 * d.w2 12454 161 + energyR16 12454 *
      radiusPolynomialRoot16 (d.w0 12454 161) (d.w1 12454 161) (d.w2 12454 161) := by
    positivity
  constructor
  · change (12454 : ℝ) ^ 8 * (mA 12454 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12454 161) (d.f1 12454 161) d.f2 + locationR16 12454 *
        radiusPolynomialRoot16 (d.f0 12454 161) (d.f1 12454 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12454 : ℝ) ^ 8 * (mA 12454 : ℝ) ^ 8 *
        ((((4812381401 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4812381401 / 1000000000000000000)) * ((401373023 / 250000000000000000)) * (126 / 100) +
          2 * (((401373023 / 250000000000000000)) ^ 2 + 2 * ((4812381401 / 1000000000000000000)) * ((385880637 / 1000000000000000000))) +
          6 * ((401373023 / 250000000000000000)) * ((385880637 / 1000000000000000000)) * (126 / 100) + 8 * ((385880637 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12454) *
          (32 * (((4812381401 / 1000000000000000000) : ℝ) + (401373023 / 250000000000000000) + (385880637 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12454 : ℝ) ^ 16 *
      (d.w0 12454 161 + d.w1 12454 161 * √(π / 2) + 2 * d.w2 12454 161 +
        energyR16 12454 * radiusPolynomialRoot16 (d.w0 12454 161) (d.w1 12454 161)
          (d.w2 12454 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12454 : ℝ) ^ 16 *
        (((971998473 / 50000000000000000000) : ℝ) + ((691558373 / 50000000000000000000)) * (126 / 100) + 2 * ((505356631 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12454) *
          (32 * (((971998473 / 50000000000000000000) : ℝ) + (691558373 / 50000000000000000000) + (505356631 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12454

/-! A coarse bound on the actual paper statistics constant at dimension 12455. -/
namespace BstLean.Part266.Row12455
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12453 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12453 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12453 128 ≤ (12707 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12707 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12455) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12455 : ℕ))
    (by norm_num : (12455 : ℕ) ≤ 16384)
  have ht : paperTail256 12455 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12455 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12455 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12455 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12455 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12455 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12453 128 * √(2 / (12455 : ℝ)) *
      (√(12455 : ℝ) + paperT0 12455 + paperTail256 12455) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12455 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12455 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12455 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12453 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12453 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12455 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12455

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12455
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12455 (61 / 100) 161 (17 / (100 * 12455)) (26 / (10 * 12455)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12455 (61 / 100) 161 (17 / (100 * 12455)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (505229111 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1622574447 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5983946633 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12455 / 12455 * (61 / 100)) ^ 4 * inverseRadius8 (12455 - 1) /
            envelopeGap 12455 (61 / 100) 161 (17 / (100 * 12455)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12455

namespace BstLean.Part266.Row12455
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12455 161 ≤ (2405708997 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12455 161 ≤ (1605170421 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (385803253 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12455 161 ≤ (971764621 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12455 161 ≤ (1382783861 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12455 161 ≤ (126308727 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (505229111 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (505229111 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1622574447 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5983946633 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3694473 / 1000000000) : ℝ) ≤ √(17 / (100 * 12455) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12455) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2247730213 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1611247689 / 40000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12455) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12455) ≤ (113545851 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12455) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12455 * (161 : ℝ) ^ 2 + 26 / (10 * 12455) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12455) : ℝ)) (tA 12455 * 161 ^ 2 + 26 / (10 * 12455)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3694473 / 1000000000))) * ((505229111 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3694473 / 1000000000)) ^ 3) * ((1622574447 / 1000000000000000000000000))) + ((5983946633 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3694473 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12455) : ℝ)) d.D d.V d.P (√(tA 12455) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3694473 / 1000000000)) ^ 2 * (((2247730213 / 1000000000000000)) * ((1611247689 / 40000000000000000)))) + ((5983946633 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12455) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3694473 / 1000000000)) * ((505229111 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12455) : ℝ)) (tA 12455 * 161 ^ 2 + 26 / (10 * 12455)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((505229111 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3694473 / 1000000000)) ^ 2) * ((1622574447 / 1000000000000000000000000)) + ((5983946633 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12455) : ℝ)) (√(26 / (10 * 12455) : ℝ)) d.D d.V d.P (√(tA 12455) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3694473 / 1000000000)) * (((2247730213 / 1000000000000000)) * ((1611247689 / 40000000000000000))) + ((5983946633 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12455) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((505229111 / 100000000000000000000) : ℝ) + ((5983946633 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12455

namespace BstLean.Part266.Row12455
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12455 161 ∧
    0 ≤ (tableEnvelope C).f1 12455 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12455 161 ∧
    0 ≤ (tableEnvelope C).w1 12455 161 ∧ 0 ≤ (tableEnvelope C).w2 12455 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12455 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12455 161 ∧ 0 ≤ d.f1 12455 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12455 161 ∧ 0 ≤ d.w1 12455 161 ∧ 0 ≤ d.w2 12455 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12455 ≤ 2 * (228 / 100 : ℝ) / 12455 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12455 ≤ 2 * (370 / 100 : ℝ) / 12455 := by
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
    (completeRAData (tableEnvelope C) 12455 161).locationBound 12455 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12455 161).energyBound 12455 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12455 161) (d.f1 12455 161) d.f2 ≤
      32 * (((2405708997 / 500000000000000000) : ℝ) + (1605170421 / 1000000000000000000) + (385803253 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12455 161) (d.w1 12455 161)
      (d.w2 12455 161) ≤
      32 * (((971764621 / 50000000000000000000) : ℝ) + (1382783861 / 100000000000000000000) + (126308727 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12455 161) (d.f1 12455 161) d.f2 ≤
      ((2405708997 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2405708997 / 500000000000000000)) * ((1605170421 / 1000000000000000000)) * (126 / 100) +
      2 * (((1605170421 / 1000000000000000000)) ^ 2 + 2 * ((2405708997 / 500000000000000000)) * ((385803253 / 1000000000000000000))) +
      6 * ((1605170421 / 1000000000000000000)) * ((385803253 / 1000000000000000000)) * (126 / 100) + 8 * ((385803253 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12455 161) (d.f1 12455 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12455 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12455 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12455 161) (d.f1 12455 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12455 161) (d.w1 12455 161) (d.w2 12455 161)
  have hwexpr0 : 0 ≤ d.w0 12455 161 + d.w1 12455 161 * √(π / 2) +
      2 * d.w2 12455 161 + energyR16 12455 *
      radiusPolynomialRoot16 (d.w0 12455 161) (d.w1 12455 161) (d.w2 12455 161) := by
    positivity
  constructor
  · change (12455 : ℝ) ^ 8 * (mA 12455 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12455 161) (d.f1 12455 161) d.f2 + locationR16 12455 *
        radiusPolynomialRoot16 (d.f0 12455 161) (d.f1 12455 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12455 : ℝ) ^ 8 * (mA 12455 : ℝ) ^ 8 *
        ((((2405708997 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2405708997 / 500000000000000000)) * ((1605170421 / 1000000000000000000)) * (126 / 100) +
          2 * (((1605170421 / 1000000000000000000)) ^ 2 + 2 * ((2405708997 / 500000000000000000)) * ((385803253 / 1000000000000000000))) +
          6 * ((1605170421 / 1000000000000000000)) * ((385803253 / 1000000000000000000)) * (126 / 100) + 8 * ((385803253 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12455) *
          (32 * (((2405708997 / 500000000000000000) : ℝ) + (1605170421 / 1000000000000000000) + (385803253 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12455 : ℝ) ^ 16 *
      (d.w0 12455 161 + d.w1 12455 161 * √(π / 2) + 2 * d.w2 12455 161 +
        energyR16 12455 * radiusPolynomialRoot16 (d.w0 12455 161) (d.w1 12455 161)
          (d.w2 12455 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12455 : ℝ) ^ 16 *
        (((971764621 / 50000000000000000000) : ℝ) + ((1382783861 / 100000000000000000000)) * (126 / 100) + 2 * ((126308727 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12455) *
          (32 * (((971764621 / 50000000000000000000) : ℝ) + (1382783861 / 100000000000000000000) + (126308727 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12455

/-! A coarse bound on the actual paper statistics constant at dimension 12456. -/
namespace BstLean.Part266.Row12456
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12454 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12454 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12454 128 ≤ (12708 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12708 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12456) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12456 : ℕ))
    (by norm_num : (12456 : ℕ) ≤ 16384)
  have ht : paperTail256 12456 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12456 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12456 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12456 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12456 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12456 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12454 128 * √(2 / (12456 : ℝ)) *
      (√(12456 : ℝ) + paperT0 12456 + paperTail256 12456) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12456 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12456 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12456 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12454 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12454 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12456 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12456

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12456
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12456 (61 / 100) 161 (17 / (100 * 12456)) (26 / (10 * 12456)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12456 (61 / 100) 161 (17 / (100 * 12456)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (505107431 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1622053431 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5980066503 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12456 / 12456 * (61 / 100)) ^ 4 * inverseRadius8 (12456 - 1) /
            envelopeGap 12456 (61 / 100) 161 (17 / (100 * 12456)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12456

namespace BstLean.Part266.Row12456
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12456 161 ≤ (962090233 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12456 161 ≤ (401211997 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (96431447 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12456 161 ≤ (971530461 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12456 161 ≤ (345612679 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12456 161 ≤ (63139153 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (505107431 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (505107431 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1622053431 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5980066503 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((147773 / 40000000) : ℝ) ≤ √(17 / (100 * 12456) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12456) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (561864881 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40274724469 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12456) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12456) ≤ (22707347 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12456) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12456 * (161 : ℝ) ^ 2 + 26 / (10 * 12456) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12456) : ℝ)) (tA 12456 * 161 ^ 2 + 26 / (10 * 12456)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((147773 / 40000000))) * ((505107431 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((147773 / 40000000)) ^ 3) * ((1622053431 / 1000000000000000000000000))) + ((5980066503 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((147773 / 40000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12456) : ℝ)) d.D d.V d.P (√(tA 12456) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((147773 / 40000000)) ^ 2 * (((561864881 / 250000000000000)) * ((40274724469 / 1000000000000000000)))) + ((5980066503 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12456) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((147773 / 40000000)) * ((505107431 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12456) : ℝ)) (tA 12456 * 161 ^ 2 + 26 / (10 * 12456)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((505107431 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((147773 / 40000000)) ^ 2) * ((1622053431 / 1000000000000000000000000)) + ((5980066503 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12456) : ℝ)) (√(26 / (10 * 12456) : ℝ)) d.D d.V d.P (√(tA 12456) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((147773 / 40000000)) * (((561864881 / 250000000000000)) * ((40274724469 / 1000000000000000000))) + ((5980066503 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12456) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((505107431 / 100000000000000000000) : ℝ) + ((5980066503 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12456

namespace BstLean.Part266.Row12456
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12456 161 ∧
    0 ≤ (tableEnvelope C).f1 12456 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12456 161 ∧
    0 ≤ (tableEnvelope C).w1 12456 161 ∧ 0 ≤ (tableEnvelope C).w2 12456 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12456 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12456 161 ∧ 0 ≤ d.f1 12456 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12456 161 ∧ 0 ≤ d.w1 12456 161 ∧ 0 ≤ d.w2 12456 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12456 ≤ 2 * (228 / 100 : ℝ) / 12456 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12456 ≤ 2 * (370 / 100 : ℝ) / 12456 := by
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
    (completeRAData (tableEnvelope C) 12456 161).locationBound 12456 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12456 161).energyBound 12456 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12456 161) (d.f1 12456 161) d.f2 ≤
      32 * (((962090233 / 200000000000000000) : ℝ) + (401211997 / 250000000000000000) + (96431447 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12456 161) (d.w1 12456 161)
      (d.w2 12456 161) ≤
      32 * (((971530461 / 50000000000000000000) : ℝ) + (345612679 / 25000000000000000000) + (63139153 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12456 161) (d.f1 12456 161) d.f2 ≤
      ((962090233 / 200000000000000000) : ℝ) ^ 2 + 2 * ((962090233 / 200000000000000000)) * ((401211997 / 250000000000000000)) * (126 / 100) +
      2 * (((401211997 / 250000000000000000)) ^ 2 + 2 * ((962090233 / 200000000000000000)) * ((96431447 / 250000000000000000))) +
      6 * ((401211997 / 250000000000000000)) * ((96431447 / 250000000000000000)) * (126 / 100) + 8 * ((96431447 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12456 161) (d.f1 12456 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12456 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12456 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12456 161) (d.f1 12456 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12456 161) (d.w1 12456 161) (d.w2 12456 161)
  have hwexpr0 : 0 ≤ d.w0 12456 161 + d.w1 12456 161 * √(π / 2) +
      2 * d.w2 12456 161 + energyR16 12456 *
      radiusPolynomialRoot16 (d.w0 12456 161) (d.w1 12456 161) (d.w2 12456 161) := by
    positivity
  constructor
  · change (12456 : ℝ) ^ 8 * (mA 12456 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12456 161) (d.f1 12456 161) d.f2 + locationR16 12456 *
        radiusPolynomialRoot16 (d.f0 12456 161) (d.f1 12456 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12456 : ℝ) ^ 8 * (mA 12456 : ℝ) ^ 8 *
        ((((962090233 / 200000000000000000) : ℝ) ^ 2 + 2 * ((962090233 / 200000000000000000)) * ((401211997 / 250000000000000000)) * (126 / 100) +
          2 * (((401211997 / 250000000000000000)) ^ 2 + 2 * ((962090233 / 200000000000000000)) * ((96431447 / 250000000000000000))) +
          6 * ((401211997 / 250000000000000000)) * ((96431447 / 250000000000000000)) * (126 / 100) + 8 * ((96431447 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12456) *
          (32 * (((962090233 / 200000000000000000) : ℝ) + (401211997 / 250000000000000000) + (96431447 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12456 : ℝ) ^ 16 *
      (d.w0 12456 161 + d.w1 12456 161 * √(π / 2) + 2 * d.w2 12456 161 +
        energyR16 12456 * radiusPolynomialRoot16 (d.w0 12456 161) (d.w1 12456 161)
          (d.w2 12456 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12456 : ℝ) ^ 16 *
        (((971530461 / 50000000000000000000) : ℝ) + ((345612679 / 25000000000000000000)) * (126 / 100) + 2 * ((63139153 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12456) *
          (32 * (((971530461 / 50000000000000000000) : ℝ) + (345612679 / 25000000000000000000) + (63139153 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12456

/-! A coarse bound on the actual paper statistics constant at dimension 12457. -/
namespace BstLean.Part266.Row12457
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12455 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12455 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12455 128 ≤ (12709 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12709 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12457) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12457 : ℕ))
    (by norm_num : (12457 : ℕ) ≤ 16384)
  have ht : paperTail256 12457 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12457 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12457 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12457 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12457 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12457 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12455 128 * √(2 / (12457 : ℝ)) *
      (√(12457 : ℝ) + paperT0 12457 + paperTail256 12457) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12457 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12457 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12457 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12455 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12455 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12457 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12457

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12457
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12457 (61 / 100) 161 (17 / (100 * 12457)) (26 / (10 * 12457)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12457 (61 / 100) 161 (17 / (100 * 12457)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (50498579 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (101345789 / 62500000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1195237841 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12457 / 12457 * (61 / 100)) ^ 4 * inverseRadius8 (12457 - 1) /
            envelopeGap 12457 (61 / 100) 161 (17 / (100 * 12457)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12457

namespace BstLean.Part266.Row12457
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12457 161 ≤ (192379387 / 40000000000000000)
  f1 : (tableEnvelope C).f1 12457 161 ≤ (80226283 / 50000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (192824173 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12457 161 ≤ (1942592767 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12457 161 ≤ (345529421 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12457 161 ≤ (25249579 / 5000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (50498579 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (50498579 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (101345789 / 62500000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1195237841 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3694177 / 1000000000) : ℝ) ≤ √(17 / (100 * 12457) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12457) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2247188889 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40268258269 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12457) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12457) ≤ (113527621 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12457) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12457 * (161 : ℝ) ^ 2 + 26 / (10 * 12457) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12457) : ℝ)) (tA 12457 * 161 ^ 2 + 26 / (10 * 12457)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3694177 / 1000000000))) * ((50498579 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3694177 / 1000000000)) ^ 3) * ((101345789 / 62500000000000000000000))) + ((1195237841 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3694177 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12457) : ℝ)) d.D d.V d.P (√(tA 12457) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3694177 / 1000000000)) ^ 2 * (((2247188889 / 1000000000000000)) * ((40268258269 / 1000000000000000000)))) + ((1195237841 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12457) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3694177 / 1000000000)) * ((50498579 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12457) : ℝ)) (tA 12457 * 161 ^ 2 + 26 / (10 * 12457)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((50498579 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3694177 / 1000000000)) ^ 2) * ((101345789 / 62500000000000000000000)) + ((1195237841 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12457) : ℝ)) (√(26 / (10 * 12457) : ℝ)) d.D d.V d.P (√(tA 12457) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3694177 / 1000000000)) * (((2247188889 / 1000000000000000)) * ((40268258269 / 1000000000000000000))) + ((1195237841 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12457) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((50498579 / 10000000000000000000) : ℝ) + ((1195237841 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12457

namespace BstLean.Part266.Row12457
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12457 161 ∧
    0 ≤ (tableEnvelope C).f1 12457 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12457 161 ∧
    0 ≤ (tableEnvelope C).w1 12457 161 ∧ 0 ≤ (tableEnvelope C).w2 12457 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12457 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12457 161 ∧ 0 ≤ d.f1 12457 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12457 161 ∧ 0 ≤ d.w1 12457 161 ∧ 0 ≤ d.w2 12457 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12457 ≤ 2 * (228 / 100 : ℝ) / 12457 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12457 ≤ 2 * (370 / 100 : ℝ) / 12457 := by
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
    (completeRAData (tableEnvelope C) 12457 161).locationBound 12457 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12457 161).energyBound 12457 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12457 161) (d.f1 12457 161) d.f2 ≤
      32 * (((192379387 / 40000000000000000) : ℝ) + (80226283 / 50000000000000000) + (192824173 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12457 161) (d.w1 12457 161)
      (d.w2 12457 161) ≤
      32 * (((1942592767 / 100000000000000000000) : ℝ) + (345529421 / 25000000000000000000) + (25249579 / 5000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12457 161) (d.f1 12457 161) d.f2 ≤
      ((192379387 / 40000000000000000) : ℝ) ^ 2 + 2 * ((192379387 / 40000000000000000)) * ((80226283 / 50000000000000000)) * (126 / 100) +
      2 * (((80226283 / 50000000000000000)) ^ 2 + 2 * ((192379387 / 40000000000000000)) * ((192824173 / 500000000000000000))) +
      6 * ((80226283 / 50000000000000000)) * ((192824173 / 500000000000000000)) * (126 / 100) + 8 * ((192824173 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12457 161) (d.f1 12457 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12457 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12457 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12457 161) (d.f1 12457 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12457 161) (d.w1 12457 161) (d.w2 12457 161)
  have hwexpr0 : 0 ≤ d.w0 12457 161 + d.w1 12457 161 * √(π / 2) +
      2 * d.w2 12457 161 + energyR16 12457 *
      radiusPolynomialRoot16 (d.w0 12457 161) (d.w1 12457 161) (d.w2 12457 161) := by
    positivity
  constructor
  · change (12457 : ℝ) ^ 8 * (mA 12457 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12457 161) (d.f1 12457 161) d.f2 + locationR16 12457 *
        radiusPolynomialRoot16 (d.f0 12457 161) (d.f1 12457 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12457 : ℝ) ^ 8 * (mA 12457 : ℝ) ^ 8 *
        ((((192379387 / 40000000000000000) : ℝ) ^ 2 + 2 * ((192379387 / 40000000000000000)) * ((80226283 / 50000000000000000)) * (126 / 100) +
          2 * (((80226283 / 50000000000000000)) ^ 2 + 2 * ((192379387 / 40000000000000000)) * ((192824173 / 500000000000000000))) +
          6 * ((80226283 / 50000000000000000)) * ((192824173 / 500000000000000000)) * (126 / 100) + 8 * ((192824173 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12457) *
          (32 * (((192379387 / 40000000000000000) : ℝ) + (80226283 / 50000000000000000) + (192824173 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12457 : ℝ) ^ 16 *
      (d.w0 12457 161 + d.w1 12457 161 * √(π / 2) + 2 * d.w2 12457 161 +
        energyR16 12457 * radiusPolynomialRoot16 (d.w0 12457 161) (d.w1 12457 161)
          (d.w2 12457 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12457 : ℝ) ^ 16 *
        (((1942592767 / 100000000000000000000) : ℝ) + ((345529421 / 25000000000000000000)) * (126 / 100) + 2 * ((25249579 / 5000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12457) *
          (32 * (((1942592767 / 100000000000000000000) : ℝ) + (345529421 / 25000000000000000000) + (25249579 / 5000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12457

/-! A coarse bound on the actual paper statistics constant at dimension 12458. -/
namespace BstLean.Part266.Row12458
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12456 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12456 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12456 128 ≤ (12710 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12710 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12458) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12458 : ℕ))
    (by norm_num : (12458 : ℕ) ≤ 16384)
  have ht : paperTail256 12458 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12458 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12458 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12458 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12458 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12458 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12456 128 * √(2 / (12458 : ℝ)) *
      (√(12458 : ℝ) + paperT0 12458 + paperTail256 12458) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12458 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12458 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12458 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12456 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12456 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12458 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12458

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12458
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12458 (61 / 100) 161 (17 / (100 * 12458)) (26 / (10 * 12458)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12458 (61 / 100) 161 (17 / (100 * 12458)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (126216047 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (810506013 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5972314739 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12458 / 12458 * (61 / 100)) ^ 4 * inverseRadius8 (12458 - 1) /
            envelopeGap 12458 (61 / 100) 161 (17 / (100 * 12458)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12458

namespace BstLean.Part266.Row12458
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12458 161 ≤ (120213057 / 25000000000000000)
  f1 : (tableEnvelope C).f1 12458 161 ≤ (1604204307 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (48196379 / 125000000000000000)
  w0 : (tableEnvelope C).w0 12458 161 ≤ (388425111 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12458 161 ≤ (1381785139 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12458 161 ≤ (252434987 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (126216047 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (126216047 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (810506013 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5972314739 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((923507 / 250000000) : ℝ) ≤ √(17 / (100 * 12458) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12458) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (561729577 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40261793627 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12458) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12458) ≤ (28379627 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12458) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12458 * (161 : ℝ) ^ 2 + 26 / (10 * 12458) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12458) : ℝ)) (tA 12458 * 161 ^ 2 + 26 / (10 * 12458)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((923507 / 250000000))) * ((126216047 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((923507 / 250000000)) ^ 3) * ((810506013 / 500000000000000000000000))) + ((5972314739 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((923507 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12458) : ℝ)) d.D d.V d.P (√(tA 12458) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((923507 / 250000000)) ^ 2 * (((561729577 / 250000000000000)) * ((40261793627 / 1000000000000000000)))) + ((5972314739 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12458) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((923507 / 250000000)) * ((126216047 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12458) : ℝ)) (tA 12458 * 161 ^ 2 + 26 / (10 * 12458)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((126216047 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((923507 / 250000000)) ^ 2) * ((810506013 / 500000000000000000000000)) + ((5972314739 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12458) : ℝ)) (√(26 / (10 * 12458) : ℝ)) d.D d.V d.P (√(tA 12458) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((923507 / 250000000)) * (((561729577 / 250000000000000)) * ((40261793627 / 1000000000000000000))) + ((5972314739 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12458) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((126216047 / 25000000000000000000) : ℝ) + ((5972314739 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12458

namespace BstLean.Part266.Row12458
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12458 161 ∧
    0 ≤ (tableEnvelope C).f1 12458 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12458 161 ∧
    0 ≤ (tableEnvelope C).w1 12458 161 ∧ 0 ≤ (tableEnvelope C).w2 12458 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12458 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12458 161 ∧ 0 ≤ d.f1 12458 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12458 161 ∧ 0 ≤ d.w1 12458 161 ∧ 0 ≤ d.w2 12458 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12458 ≤ 2 * (228 / 100 : ℝ) / 12458 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12458 ≤ 2 * (370 / 100 : ℝ) / 12458 := by
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
    (completeRAData (tableEnvelope C) 12458 161).locationBound 12458 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12458 161).energyBound 12458 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12458 161) (d.f1 12458 161) d.f2 ≤
      32 * (((120213057 / 25000000000000000) : ℝ) + (1604204307 / 1000000000000000000) + (48196379 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12458 161) (d.w1 12458 161)
      (d.w2 12458 161) ≤
      32 * (((388425111 / 20000000000000000000) : ℝ) + (1381785139 / 100000000000000000000) + (252434987 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12458 161) (d.f1 12458 161) d.f2 ≤
      ((120213057 / 25000000000000000) : ℝ) ^ 2 + 2 * ((120213057 / 25000000000000000)) * ((1604204307 / 1000000000000000000)) * (126 / 100) +
      2 * (((1604204307 / 1000000000000000000)) ^ 2 + 2 * ((120213057 / 25000000000000000)) * ((48196379 / 125000000000000000))) +
      6 * ((1604204307 / 1000000000000000000)) * ((48196379 / 125000000000000000)) * (126 / 100) + 8 * ((48196379 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12458 161) (d.f1 12458 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12458 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12458 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12458 161) (d.f1 12458 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12458 161) (d.w1 12458 161) (d.w2 12458 161)
  have hwexpr0 : 0 ≤ d.w0 12458 161 + d.w1 12458 161 * √(π / 2) +
      2 * d.w2 12458 161 + energyR16 12458 *
      radiusPolynomialRoot16 (d.w0 12458 161) (d.w1 12458 161) (d.w2 12458 161) := by
    positivity
  constructor
  · change (12458 : ℝ) ^ 8 * (mA 12458 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12458 161) (d.f1 12458 161) d.f2 + locationR16 12458 *
        radiusPolynomialRoot16 (d.f0 12458 161) (d.f1 12458 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12458 : ℝ) ^ 8 * (mA 12458 : ℝ) ^ 8 *
        ((((120213057 / 25000000000000000) : ℝ) ^ 2 + 2 * ((120213057 / 25000000000000000)) * ((1604204307 / 1000000000000000000)) * (126 / 100) +
          2 * (((1604204307 / 1000000000000000000)) ^ 2 + 2 * ((120213057 / 25000000000000000)) * ((48196379 / 125000000000000000))) +
          6 * ((1604204307 / 1000000000000000000)) * ((48196379 / 125000000000000000)) * (126 / 100) + 8 * ((48196379 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12458) *
          (32 * (((120213057 / 25000000000000000) : ℝ) + (1604204307 / 1000000000000000000) + (48196379 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12458 : ℝ) ^ 16 *
      (d.w0 12458 161 + d.w1 12458 161 * √(π / 2) + 2 * d.w2 12458 161 +
        energyR16 12458 * radiusPolynomialRoot16 (d.w0 12458 161) (d.w1 12458 161)
          (d.w2 12458 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12458 : ℝ) ^ 16 *
        (((388425111 / 20000000000000000000) : ℝ) + ((1381785139 / 100000000000000000000)) * (126 / 100) + 2 * ((252434987 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12458) *
          (32 * (((388425111 / 20000000000000000000) : ℝ) + (1381785139 / 100000000000000000000) + (252434987 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12458

/-! A coarse bound on the actual paper statistics constant at dimension 12459. -/
namespace BstLean.Part266.Row12459
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12457 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12457 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12457 128 ≤ (12711 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12711 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12459) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12459 : ℕ))
    (by norm_num : (12459 : ℕ) ≤ 16384)
  have ht : paperTail256 12459 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12459 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12459 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12459 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12459 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12459 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12457 128 * √(2 / (12459 : ℝ)) *
      (√(12459 : ℝ) + paperT0 12459 + paperTail256 12459) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12459 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12459 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12459 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12457 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12457 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12459 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12459

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12459
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12459 (61 / 100) 161 (17 / (100 * 12459)) (26 / (10 * 12459)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12459 (61 / 100) 161 (17 / (100 * 12459)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (4037941 / 800000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1620491637 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5968443101 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12459 / 12459 * (61 / 100)) ^ 4 * inverseRadius8 (12459 - 1) /
            envelopeGap 12459 (61 / 100) 161 (17 / (100 * 12459)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12459

namespace BstLean.Part266.Row12459
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12459 161 ≤ (4807556467 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12459 161 ≤ (1603882191 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (192746819 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12459 161 ≤ (15169201 / 781250000000000000)
  w1 : (tableEnvelope C).w1 12459 161 ≤ (690726167 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12459 161 ≤ (504748407 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (4037941 / 800000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (4037941 / 800000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1620491637 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5968443101 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((92347 / 25000000) : ℝ) ≤ √(17 / (100 * 12459) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12459) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2246647781 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (20127665271 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12459) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12459) ≤ (28377349 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12459) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12459 * (161 : ℝ) ^ 2 + 26 / (10 * 12459) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12459) : ℝ)) (tA 12459 * 161 ^ 2 + 26 / (10 * 12459)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((92347 / 25000000))) * ((4037941 / 800000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((92347 / 25000000)) ^ 3) * ((1620491637 / 1000000000000000000000000))) + ((5968443101 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((92347 / 25000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12459) : ℝ)) d.D d.V d.P (√(tA 12459) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((92347 / 25000000)) ^ 2 * (((2246647781 / 1000000000000000)) * ((20127665271 / 500000000000000000)))) + ((5968443101 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12459) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((92347 / 25000000)) * ((4037941 / 800000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12459) : ℝ)) (tA 12459 * 161 ^ 2 + 26 / (10 * 12459)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((4037941 / 800000000000000000) : ℝ) + (24198 / 100000) / (2 * ((92347 / 25000000)) ^ 2) * ((1620491637 / 1000000000000000000000000)) + ((5968443101 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12459) : ℝ)) (√(26 / (10 * 12459) : ℝ)) d.D d.V d.P (√(tA 12459) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((92347 / 25000000)) * (((2246647781 / 1000000000000000)) * ((20127665271 / 500000000000000000))) + ((5968443101 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12459) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((4037941 / 800000000000000000) : ℝ) + ((5968443101 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12459

namespace BstLean.Part266.Row12459
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12459 161 ∧
    0 ≤ (tableEnvelope C).f1 12459 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12459 161 ∧
    0 ≤ (tableEnvelope C).w1 12459 161 ∧ 0 ≤ (tableEnvelope C).w2 12459 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12459 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12459 161 ∧ 0 ≤ d.f1 12459 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12459 161 ∧ 0 ≤ d.w1 12459 161 ∧ 0 ≤ d.w2 12459 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12459 ≤ 2 * (228 / 100 : ℝ) / 12459 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12459 ≤ 2 * (370 / 100 : ℝ) / 12459 := by
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
    (completeRAData (tableEnvelope C) 12459 161).locationBound 12459 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12459 161).energyBound 12459 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12459 161) (d.f1 12459 161) d.f2 ≤
      32 * (((4807556467 / 1000000000000000000) : ℝ) + (1603882191 / 1000000000000000000) + (192746819 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12459 161) (d.w1 12459 161)
      (d.w2 12459 161) ≤
      32 * (((15169201 / 781250000000000000) : ℝ) + (690726167 / 50000000000000000000) + (504748407 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12459 161) (d.f1 12459 161) d.f2 ≤
      ((4807556467 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4807556467 / 1000000000000000000)) * ((1603882191 / 1000000000000000000)) * (126 / 100) +
      2 * (((1603882191 / 1000000000000000000)) ^ 2 + 2 * ((4807556467 / 1000000000000000000)) * ((192746819 / 500000000000000000))) +
      6 * ((1603882191 / 1000000000000000000)) * ((192746819 / 500000000000000000)) * (126 / 100) + 8 * ((192746819 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12459 161) (d.f1 12459 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12459 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12459 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12459 161) (d.f1 12459 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12459 161) (d.w1 12459 161) (d.w2 12459 161)
  have hwexpr0 : 0 ≤ d.w0 12459 161 + d.w1 12459 161 * √(π / 2) +
      2 * d.w2 12459 161 + energyR16 12459 *
      radiusPolynomialRoot16 (d.w0 12459 161) (d.w1 12459 161) (d.w2 12459 161) := by
    positivity
  constructor
  · change (12459 : ℝ) ^ 8 * (mA 12459 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12459 161) (d.f1 12459 161) d.f2 + locationR16 12459 *
        radiusPolynomialRoot16 (d.f0 12459 161) (d.f1 12459 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12459 : ℝ) ^ 8 * (mA 12459 : ℝ) ^ 8 *
        ((((4807556467 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4807556467 / 1000000000000000000)) * ((1603882191 / 1000000000000000000)) * (126 / 100) +
          2 * (((1603882191 / 1000000000000000000)) ^ 2 + 2 * ((4807556467 / 1000000000000000000)) * ((192746819 / 500000000000000000))) +
          6 * ((1603882191 / 1000000000000000000)) * ((192746819 / 500000000000000000)) * (126 / 100) + 8 * ((192746819 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12459) *
          (32 * (((4807556467 / 1000000000000000000) : ℝ) + (1603882191 / 1000000000000000000) + (192746819 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12459 : ℝ) ^ 16 *
      (d.w0 12459 161 + d.w1 12459 161 * √(π / 2) + 2 * d.w2 12459 161 +
        energyR16 12459 * radiusPolynomialRoot16 (d.w0 12459 161) (d.w1 12459 161)
          (d.w2 12459 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12459 : ℝ) ^ 16 *
        (((15169201 / 781250000000000000) : ℝ) + ((690726167 / 50000000000000000000)) * (126 / 100) + 2 * ((504748407 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12459) *
          (32 * (((15169201 / 781250000000000000) : ℝ) + (690726167 / 50000000000000000000) + (504748407 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12459

/-! A coarse bound on the actual paper statistics constant at dimension 12460. -/
namespace BstLean.Part266.Row12460
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12458 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12458 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12458 128 ≤ (12712 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12712 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12460) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12460 : ℕ))
    (by norm_num : (12460 : ℕ) ≤ 16384)
  have ht : paperTail256 12460 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12460 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12460 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12460 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12460 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12460 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12458 128 * √(2 / (12460 : ℝ)) *
      (√(12460 : ℝ) + paperT0 12460 + paperTail256 12460) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12460 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12460 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12460 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12458 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12458 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12460 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12460

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12460
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12460 (61 / 100) 161 (17 / (100 * 12460)) (26 / (10 * 12460)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12460 (61 / 100) 161 (17 / (100 * 12460)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (504621101 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1619971457 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (596457429 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12460 / 12460 * (61 / 100)) ^ 4 * inverseRadius8 (12460 - 1) /
            envelopeGap 12460 (61 / 100) 161 (17 / (100 * 12460)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12460

namespace BstLean.Part266.Row12460
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12460 161 ≤ (300411937 / 62500000000000000)
  f1 : (tableEnvelope C).f1 12460 161 ≤ (801780091 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (385416267 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12460 161 ≤ (388238013 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12460 161 ≤ (1381119643 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12460 161 ≤ (504626879 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (504621101 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (504621101 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1619971457 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (596457429 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((923433 / 250000000) : ℝ) ≤ √(17 / (100 * 12460) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12460) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2246377309 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (5031108627 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12460) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12460) ≤ (56750143 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12460) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12460 * (161 : ℝ) ^ 2 + 26 / (10 * 12460) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12460) : ℝ)) (tA 12460 * 161 ^ 2 + 26 / (10 * 12460)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((923433 / 250000000))) * ((504621101 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((923433 / 250000000)) ^ 3) * ((1619971457 / 1000000000000000000000000))) + ((596457429 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((923433 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12460) : ℝ)) d.D d.V d.P (√(tA 12460) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((923433 / 250000000)) ^ 2 * (((2246377309 / 1000000000000000)) * ((5031108627 / 125000000000000000)))) + ((596457429 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12460) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((923433 / 250000000)) * ((504621101 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12460) : ℝ)) (tA 12460 * 161 ^ 2 + 26 / (10 * 12460)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((504621101 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((923433 / 250000000)) ^ 2) * ((1619971457 / 1000000000000000000000000)) + ((596457429 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12460) : ℝ)) (√(26 / (10 * 12460) : ℝ)) d.D d.V d.P (√(tA 12460) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((923433 / 250000000)) * (((2246377309 / 1000000000000000)) * ((5031108627 / 125000000000000000))) + ((596457429 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12460) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((504621101 / 100000000000000000000) : ℝ) + ((596457429 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12460

namespace BstLean.Part266.Row12460
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12460 161 ∧
    0 ≤ (tableEnvelope C).f1 12460 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12460 161 ∧
    0 ≤ (tableEnvelope C).w1 12460 161 ∧ 0 ≤ (tableEnvelope C).w2 12460 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12460 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12460 161 ∧ 0 ≤ d.f1 12460 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12460 161 ∧ 0 ≤ d.w1 12460 161 ∧ 0 ≤ d.w2 12460 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12460 ≤ 2 * (228 / 100 : ℝ) / 12460 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12460 ≤ 2 * (370 / 100 : ℝ) / 12460 := by
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
    (completeRAData (tableEnvelope C) 12460 161).locationBound 12460 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12460 161).energyBound 12460 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12460 161) (d.f1 12460 161) d.f2 ≤
      32 * (((300411937 / 62500000000000000) : ℝ) + (801780091 / 500000000000000000) + (385416267 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12460 161) (d.w1 12460 161)
      (d.w2 12460 161) ≤
      32 * (((388238013 / 20000000000000000000) : ℝ) + (1381119643 / 100000000000000000000) + (504626879 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12460 161) (d.f1 12460 161) d.f2 ≤
      ((300411937 / 62500000000000000) : ℝ) ^ 2 + 2 * ((300411937 / 62500000000000000)) * ((801780091 / 500000000000000000)) * (126 / 100) +
      2 * (((801780091 / 500000000000000000)) ^ 2 + 2 * ((300411937 / 62500000000000000)) * ((385416267 / 1000000000000000000))) +
      6 * ((801780091 / 500000000000000000)) * ((385416267 / 1000000000000000000)) * (126 / 100) + 8 * ((385416267 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12460 161) (d.f1 12460 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12460 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12460 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12460 161) (d.f1 12460 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12460 161) (d.w1 12460 161) (d.w2 12460 161)
  have hwexpr0 : 0 ≤ d.w0 12460 161 + d.w1 12460 161 * √(π / 2) +
      2 * d.w2 12460 161 + energyR16 12460 *
      radiusPolynomialRoot16 (d.w0 12460 161) (d.w1 12460 161) (d.w2 12460 161) := by
    positivity
  constructor
  · change (12460 : ℝ) ^ 8 * (mA 12460 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12460 161) (d.f1 12460 161) d.f2 + locationR16 12460 *
        radiusPolynomialRoot16 (d.f0 12460 161) (d.f1 12460 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12460 : ℝ) ^ 8 * (mA 12460 : ℝ) ^ 8 *
        ((((300411937 / 62500000000000000) : ℝ) ^ 2 + 2 * ((300411937 / 62500000000000000)) * ((801780091 / 500000000000000000)) * (126 / 100) +
          2 * (((801780091 / 500000000000000000)) ^ 2 + 2 * ((300411937 / 62500000000000000)) * ((385416267 / 1000000000000000000))) +
          6 * ((801780091 / 500000000000000000)) * ((385416267 / 1000000000000000000)) * (126 / 100) + 8 * ((385416267 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12460) *
          (32 * (((300411937 / 62500000000000000) : ℝ) + (801780091 / 500000000000000000) + (385416267 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12460 : ℝ) ^ 16 *
      (d.w0 12460 161 + d.w1 12460 161 * √(π / 2) + 2 * d.w2 12460 161 +
        energyR16 12460 * radiusPolynomialRoot16 (d.w0 12460 161) (d.w1 12460 161)
          (d.w2 12460 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12460 : ℝ) ^ 16 *
        (((388238013 / 20000000000000000000) : ℝ) + ((1381119643 / 100000000000000000000)) * (126 / 100) + 2 * ((504626879 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12460) *
          (32 * (((388238013 / 20000000000000000000) : ℝ) + (1381119643 / 100000000000000000000) + (504626879 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12460

/-! A coarse bound on the actual paper statistics constant at dimension 12461. -/
namespace BstLean.Part266.Row12461
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12459 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12459 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12459 128 ≤ (12713 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12713 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12461) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12461 : ℕ))
    (by norm_num : (12461 : ℕ) ≤ 16384)
  have ht : paperTail256 12461 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12461 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12461 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12461 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12461 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12461 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12459 128 * √(2 / (12461 : ℝ)) *
      (√(12461 : ℝ) + paperT0 12461 + paperTail256 12461) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12461 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12461 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12461 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12459 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12459 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12461 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12461

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12461
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12461 (61 / 100) 161 (17 / (100 * 12461)) (26 / (10 * 12461)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12461 (61 / 100) 161 (17 / (100 * 12461)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (15765613 / 3125000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (323890297 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2980354151 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12461 / 12461 * (61 / 100)) ^ 4 * inverseRadius8 (12461 - 1) /
            envelopeGap 12461 (61 / 100) 161 (17 / (100 * 12461)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12461

namespace BstLean.Part266.Row12461
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12461 161 ≤ (2402812927 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12461 161 ≤ (1603238277 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (9633473 / 25000000000000000)
  w0 : (tableEnvelope C).w0 12461 161 ≤ (970361283 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12461 161 ≤ (172598383 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 12461 161 ≤ (504505391 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (15765613 / 3125000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (15765613 / 3125000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (323890297 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2980354151 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((230849 / 62500000) : ℝ) ≤ √(17 / (100 * 12461) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12461) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (224610689 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (10060602259 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12461) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12461) ≤ (56745589 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12461) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12461 * (161 : ℝ) ^ 2 + 26 / (10 * 12461) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12461) : ℝ)) (tA 12461 * 161 ^ 2 + 26 / (10 * 12461)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((230849 / 62500000))) * ((15765613 / 3125000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((230849 / 62500000)) ^ 3) * ((323890297 / 200000000000000000000000))) + ((2980354151 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((230849 / 62500000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12461) : ℝ)) d.D d.V d.P (√(tA 12461) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((230849 / 62500000)) ^ 2 * (((224610689 / 100000000000000)) * ((10060602259 / 250000000000000000)))) + ((2980354151 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12461) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((230849 / 62500000)) * ((15765613 / 3125000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12461) : ℝ)) (tA 12461 * 161 ^ 2 + 26 / (10 * 12461)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((15765613 / 3125000000000000000) : ℝ) + (24198 / 100000) / (2 * ((230849 / 62500000)) ^ 2) * ((323890297 / 200000000000000000000000)) + ((2980354151 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12461) : ℝ)) (√(26 / (10 * 12461) : ℝ)) d.D d.V d.P (√(tA 12461) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((230849 / 62500000)) * (((224610689 / 100000000000000)) * ((10060602259 / 250000000000000000))) + ((2980354151 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12461) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((15765613 / 3125000000000000000) : ℝ) + ((2980354151 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12461

namespace BstLean.Part266.Row12461
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12461 161 ∧
    0 ≤ (tableEnvelope C).f1 12461 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12461 161 ∧
    0 ≤ (tableEnvelope C).w1 12461 161 ∧ 0 ≤ (tableEnvelope C).w2 12461 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12461 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12461 161 ∧ 0 ≤ d.f1 12461 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12461 161 ∧ 0 ≤ d.w1 12461 161 ∧ 0 ≤ d.w2 12461 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12461 ≤ 2 * (228 / 100 : ℝ) / 12461 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12461 ≤ 2 * (370 / 100 : ℝ) / 12461 := by
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
    (completeRAData (tableEnvelope C) 12461 161).locationBound 12461 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12461 161).energyBound 12461 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12461 161) (d.f1 12461 161) d.f2 ≤
      32 * (((2402812927 / 500000000000000000) : ℝ) + (1603238277 / 1000000000000000000) + (9633473 / 25000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12461 161) (d.w1 12461 161)
      (d.w2 12461 161) ≤
      32 * (((970361283 / 50000000000000000000) : ℝ) + (172598383 / 12500000000000000000) + (504505391 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12461 161) (d.f1 12461 161) d.f2 ≤
      ((2402812927 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2402812927 / 500000000000000000)) * ((1603238277 / 1000000000000000000)) * (126 / 100) +
      2 * (((1603238277 / 1000000000000000000)) ^ 2 + 2 * ((2402812927 / 500000000000000000)) * ((9633473 / 25000000000000000))) +
      6 * ((1603238277 / 1000000000000000000)) * ((9633473 / 25000000000000000)) * (126 / 100) + 8 * ((9633473 / 25000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12461 161) (d.f1 12461 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12461 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12461 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12461 161) (d.f1 12461 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12461 161) (d.w1 12461 161) (d.w2 12461 161)
  have hwexpr0 : 0 ≤ d.w0 12461 161 + d.w1 12461 161 * √(π / 2) +
      2 * d.w2 12461 161 + energyR16 12461 *
      radiusPolynomialRoot16 (d.w0 12461 161) (d.w1 12461 161) (d.w2 12461 161) := by
    positivity
  constructor
  · change (12461 : ℝ) ^ 8 * (mA 12461 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12461 161) (d.f1 12461 161) d.f2 + locationR16 12461 *
        radiusPolynomialRoot16 (d.f0 12461 161) (d.f1 12461 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12461 : ℝ) ^ 8 * (mA 12461 : ℝ) ^ 8 *
        ((((2402812927 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2402812927 / 500000000000000000)) * ((1603238277 / 1000000000000000000)) * (126 / 100) +
          2 * (((1603238277 / 1000000000000000000)) ^ 2 + 2 * ((2402812927 / 500000000000000000)) * ((9633473 / 25000000000000000))) +
          6 * ((1603238277 / 1000000000000000000)) * ((9633473 / 25000000000000000)) * (126 / 100) + 8 * ((9633473 / 25000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12461) *
          (32 * (((2402812927 / 500000000000000000) : ℝ) + (1603238277 / 1000000000000000000) + (9633473 / 25000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12461 : ℝ) ^ 16 *
      (d.w0 12461 161 + d.w1 12461 161 * √(π / 2) + 2 * d.w2 12461 161 +
        energyR16 12461 * radiusPolynomialRoot16 (d.w0 12461 161) (d.w1 12461 161)
          (d.w2 12461 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12461 : ℝ) ^ 16 *
        (((970361283 / 50000000000000000000) : ℝ) + ((172598383 / 12500000000000000000)) * (126 / 100) + 2 * ((504505391 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12461) *
          (32 * (((970361283 / 50000000000000000000) : ℝ) + (172598383 / 12500000000000000000) + (504505391 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12461

/-! A coarse bound on the actual paper statistics constant at dimension 12462. -/
namespace BstLean.Part266.Row12462
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12460 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12460 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12460 128 ≤ (12714 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12714 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12462) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12462 : ℕ))
    (by norm_num : (12462 : ℕ) ≤ 16384)
  have ht : paperTail256 12462 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12462 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12462 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12462 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12462 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12462 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12460 128 * √(2 / (12462 : ℝ)) *
      (√(12462 : ℝ) + paperT0 12462 + paperTail256 12462) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12462 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12462 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12462 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12460 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12460 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12462 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12462

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12462
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12462 (61 / 100) 161 (17 / (100 * 12462)) (26 / (10 * 12462)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12462 (61 / 100) 161 (17 / (100 * 12462)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (50437817 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (809465861 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5956845137 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12462 / 12462 * (61 / 100)) ^ 4 * inverseRadius8 (12462 - 1) /
            envelopeGap 12462 (61 / 100) 161 (17 / (100 * 12462)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12462

namespace BstLean.Part266.Row12462
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12462 161 ≤ (2402330527 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12462 161 ≤ (1602916479 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (96315399 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12462 161 ≤ (1940255231 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12462 161 ≤ (6902273 / 500000000000000000)
  w2 : (tableEnvelope C).w2 12462 161 ≤ (504383941 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (50437817 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (50437817 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (809465861 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5956845137 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((923359 / 250000000) : ℝ) ≤ √(17 / (100 * 12462) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12462) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1122918263 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40235950617 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12462) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12462) ≤ (113482071 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12462) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12462 * (161 : ℝ) ^ 2 + 26 / (10 * 12462) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12462) : ℝ)) (tA 12462 * 161 ^ 2 + 26 / (10 * 12462)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((923359 / 250000000))) * ((50437817 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((923359 / 250000000)) ^ 3) * ((809465861 / 500000000000000000000000))) + ((5956845137 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((923359 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12462) : ℝ)) d.D d.V d.P (√(tA 12462) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((923359 / 250000000)) ^ 2 * (((1122918263 / 500000000000000)) * ((40235950617 / 1000000000000000000)))) + ((5956845137 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12462) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((923359 / 250000000)) * ((50437817 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12462) : ℝ)) (tA 12462 * 161 ^ 2 + 26 / (10 * 12462)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((50437817 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((923359 / 250000000)) ^ 2) * ((809465861 / 500000000000000000000000)) + ((5956845137 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12462) : ℝ)) (√(26 / (10 * 12462) : ℝ)) d.D d.V d.P (√(tA 12462) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((923359 / 250000000)) * (((1122918263 / 500000000000000)) * ((40235950617 / 1000000000000000000))) + ((5956845137 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12462) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((50437817 / 10000000000000000000) : ℝ) + ((5956845137 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12462

namespace BstLean.Part266.Row12462
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12462 161 ∧
    0 ≤ (tableEnvelope C).f1 12462 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12462 161 ∧
    0 ≤ (tableEnvelope C).w1 12462 161 ∧ 0 ≤ (tableEnvelope C).w2 12462 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12462 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12462 161 ∧ 0 ≤ d.f1 12462 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12462 161 ∧ 0 ≤ d.w1 12462 161 ∧ 0 ≤ d.w2 12462 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12462 ≤ 2 * (228 / 100 : ℝ) / 12462 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12462 ≤ 2 * (370 / 100 : ℝ) / 12462 := by
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
    (completeRAData (tableEnvelope C) 12462 161).locationBound 12462 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12462 161).energyBound 12462 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12462 161) (d.f1 12462 161) d.f2 ≤
      32 * (((2402330527 / 500000000000000000) : ℝ) + (1602916479 / 1000000000000000000) + (96315399 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12462 161) (d.w1 12462 161)
      (d.w2 12462 161) ≤
      32 * (((1940255231 / 100000000000000000000) : ℝ) + (6902273 / 500000000000000000) + (504383941 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12462 161) (d.f1 12462 161) d.f2 ≤
      ((2402330527 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2402330527 / 500000000000000000)) * ((1602916479 / 1000000000000000000)) * (126 / 100) +
      2 * (((1602916479 / 1000000000000000000)) ^ 2 + 2 * ((2402330527 / 500000000000000000)) * ((96315399 / 250000000000000000))) +
      6 * ((1602916479 / 1000000000000000000)) * ((96315399 / 250000000000000000)) * (126 / 100) + 8 * ((96315399 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12462 161) (d.f1 12462 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12462 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12462 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12462 161) (d.f1 12462 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12462 161) (d.w1 12462 161) (d.w2 12462 161)
  have hwexpr0 : 0 ≤ d.w0 12462 161 + d.w1 12462 161 * √(π / 2) +
      2 * d.w2 12462 161 + energyR16 12462 *
      radiusPolynomialRoot16 (d.w0 12462 161) (d.w1 12462 161) (d.w2 12462 161) := by
    positivity
  constructor
  · change (12462 : ℝ) ^ 8 * (mA 12462 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12462 161) (d.f1 12462 161) d.f2 + locationR16 12462 *
        radiusPolynomialRoot16 (d.f0 12462 161) (d.f1 12462 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12462 : ℝ) ^ 8 * (mA 12462 : ℝ) ^ 8 *
        ((((2402330527 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2402330527 / 500000000000000000)) * ((1602916479 / 1000000000000000000)) * (126 / 100) +
          2 * (((1602916479 / 1000000000000000000)) ^ 2 + 2 * ((2402330527 / 500000000000000000)) * ((96315399 / 250000000000000000))) +
          6 * ((1602916479 / 1000000000000000000)) * ((96315399 / 250000000000000000)) * (126 / 100) + 8 * ((96315399 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12462) *
          (32 * (((2402330527 / 500000000000000000) : ℝ) + (1602916479 / 1000000000000000000) + (96315399 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12462 : ℝ) ^ 16 *
      (d.w0 12462 161 + d.w1 12462 161 * √(π / 2) + 2 * d.w2 12462 161 +
        energyR16 12462 * radiusPolynomialRoot16 (d.w0 12462 161) (d.w1 12462 161)
          (d.w2 12462 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12462 : ℝ) ^ 16 *
        (((1940255231 / 100000000000000000000) : ℝ) + ((6902273 / 500000000000000000)) * (126 / 100) + 2 * ((504383941 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12462) *
          (32 * (((1940255231 / 100000000000000000000) : ℝ) + (6902273 / 500000000000000000) + (504383941 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12462

/-! A coarse bound on the actual paper statistics constant at dimension 12463. -/
namespace BstLean.Part266.Row12463
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12461 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12461 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12461 128 ≤ (12715 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12715 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12463) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12463 : ℕ))
    (by norm_num : (12463 : ℕ) ≤ 16384)
  have ht : paperTail256 12463 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12463 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12463 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12463 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12463 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12463 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12461 128 * √(2 / (12463 : ℝ)) *
      (√(12463 : ℝ) + paperT0 12463 + paperTail256 12463) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12463 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12463 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12463 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12461 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12461 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12463 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12463

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12463
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12463 (61 / 100) 161 (17 / (100 * 12463)) (26 / (10 * 12463)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12463 (61 / 100) 161 (17 / (100 * 12463)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (126064191 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1618412167 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (595298479 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12463 / 12463 * (61 / 100)) ^ 4 * inverseRadius8 (12463 - 1) /
            envelopeGap 12463 (61 / 100) 161 (17 / (100 * 12463)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12463

namespace BstLean.Part266.Row12463
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12463 161 ≤ (2401850173 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12463 161 ≤ (200324457 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (385184401 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12463 161 ≤ (969894419 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12463 161 ≤ (21059 / 1525878906250000)
  w2 : (tableEnvelope C).w2 12463 161 ≤ (504262531 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (126064191 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (126064191 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1618412167 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (595298479 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3693287 / 1000000000) : ℝ) ≤ √(17 / (100 * 12463) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12463) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2245566219 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (20114746873 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12463) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12463) ≤ (22694593 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12463) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12463 * (161 : ℝ) ^ 2 + 26 / (10 * 12463) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12463) : ℝ)) (tA 12463 * 161 ^ 2 + 26 / (10 * 12463)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3693287 / 1000000000))) * ((126064191 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3693287 / 1000000000)) ^ 3) * ((1618412167 / 1000000000000000000000000))) + ((595298479 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3693287 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12463) : ℝ)) d.D d.V d.P (√(tA 12463) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3693287 / 1000000000)) ^ 2 * (((2245566219 / 1000000000000000)) * ((20114746873 / 500000000000000000)))) + ((595298479 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12463) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3693287 / 1000000000)) * ((126064191 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12463) : ℝ)) (tA 12463 * 161 ^ 2 + 26 / (10 * 12463)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((126064191 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3693287 / 1000000000)) ^ 2) * ((1618412167 / 1000000000000000000000000)) + ((595298479 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12463) : ℝ)) (√(26 / (10 * 12463) : ℝ)) d.D d.V d.P (√(tA 12463) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3693287 / 1000000000)) * (((2245566219 / 1000000000000000)) * ((20114746873 / 500000000000000000))) + ((595298479 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12463) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((126064191 / 25000000000000000000) : ℝ) + ((595298479 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12463

namespace BstLean.Part266.Row12463
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12463 161 ∧
    0 ≤ (tableEnvelope C).f1 12463 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12463 161 ∧
    0 ≤ (tableEnvelope C).w1 12463 161 ∧ 0 ≤ (tableEnvelope C).w2 12463 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12463 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12463 161 ∧ 0 ≤ d.f1 12463 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12463 161 ∧ 0 ≤ d.w1 12463 161 ∧ 0 ≤ d.w2 12463 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12463 ≤ 2 * (228 / 100 : ℝ) / 12463 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12463 ≤ 2 * (370 / 100 : ℝ) / 12463 := by
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
    (completeRAData (tableEnvelope C) 12463 161).locationBound 12463 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12463 161).energyBound 12463 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12463 161) (d.f1 12463 161) d.f2 ≤
      32 * (((2401850173 / 500000000000000000) : ℝ) + (200324457 / 125000000000000000) + (385184401 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12463 161) (d.w1 12463 161)
      (d.w2 12463 161) ≤
      32 * (((969894419 / 50000000000000000000) : ℝ) + (21059 / 1525878906250000) + (504262531 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12463 161) (d.f1 12463 161) d.f2 ≤
      ((2401850173 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2401850173 / 500000000000000000)) * ((200324457 / 125000000000000000)) * (126 / 100) +
      2 * (((200324457 / 125000000000000000)) ^ 2 + 2 * ((2401850173 / 500000000000000000)) * ((385184401 / 1000000000000000000))) +
      6 * ((200324457 / 125000000000000000)) * ((385184401 / 1000000000000000000)) * (126 / 100) + 8 * ((385184401 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12463 161) (d.f1 12463 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12463 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12463 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12463 161) (d.f1 12463 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12463 161) (d.w1 12463 161) (d.w2 12463 161)
  have hwexpr0 : 0 ≤ d.w0 12463 161 + d.w1 12463 161 * √(π / 2) +
      2 * d.w2 12463 161 + energyR16 12463 *
      radiusPolynomialRoot16 (d.w0 12463 161) (d.w1 12463 161) (d.w2 12463 161) := by
    positivity
  constructor
  · change (12463 : ℝ) ^ 8 * (mA 12463 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12463 161) (d.f1 12463 161) d.f2 + locationR16 12463 *
        radiusPolynomialRoot16 (d.f0 12463 161) (d.f1 12463 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12463 : ℝ) ^ 8 * (mA 12463 : ℝ) ^ 8 *
        ((((2401850173 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2401850173 / 500000000000000000)) * ((200324457 / 125000000000000000)) * (126 / 100) +
          2 * (((200324457 / 125000000000000000)) ^ 2 + 2 * ((2401850173 / 500000000000000000)) * ((385184401 / 1000000000000000000))) +
          6 * ((200324457 / 125000000000000000)) * ((385184401 / 1000000000000000000)) * (126 / 100) + 8 * ((385184401 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12463) *
          (32 * (((2401850173 / 500000000000000000) : ℝ) + (200324457 / 125000000000000000) + (385184401 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12463 : ℝ) ^ 16 *
      (d.w0 12463 161 + d.w1 12463 161 * √(π / 2) + 2 * d.w2 12463 161 +
        energyR16 12463 * radiusPolynomialRoot16 (d.w0 12463 161) (d.w1 12463 161)
          (d.w2 12463 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12463 : ℝ) ^ 16 *
        (((969894419 / 50000000000000000000) : ℝ) + ((21059 / 1525878906250000)) * (126 / 100) + 2 * ((504262531 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12463) *
          (32 * (((969894419 / 50000000000000000000) : ℝ) + (21059 / 1525878906250000) + (504262531 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12463

/-! A coarse bound on the actual paper statistics constant at dimension 12464. -/
namespace BstLean.Part266.Row12464
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12462 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12462 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12462 128 ≤ (12716 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12716 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12464) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12464 : ℕ))
    (by norm_num : (12464 : ℕ) ≤ 16384)
  have ht : paperTail256 12464 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12464 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12464 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12464 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12464 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12464 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12462 128 * √(2 / (12464 : ℝ)) *
      (√(12464 : ℝ) + paperT0 12464 + paperTail256 12464) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12464 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12464 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12464 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12462 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12462 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12464 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12464

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12464
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12464 (61 / 100) 161 (17 / (100 * 12464)) (26 / (10 * 12464)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12464 (61 / 100) 161 (17 / (100 * 12464)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (126033849 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1617892821 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5949127261 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12464 / 12464 * (61 / 100)) ^ 4 * inverseRadius8 (12464 - 1) /
            envelopeGap 12464 (61 / 100) 161 (17 / (100 * 12464)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12464

namespace BstLean.Part266.Row12464
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12464 161 ≤ (4802736223 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12464 161 ≤ (160227407 / 100000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (96276781 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12464 161 ≤ (1939321831 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12464 161 ≤ (689895193 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12464 161 ≤ (504141159 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (126033849 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (126033849 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1617892821 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5949127261 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3693139 / 1000000000) : ℝ) ≤ √(17 / (100 * 12464) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12464) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2245295963 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (10055759609 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12464) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12464) ≤ (113463861 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12464) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12464 * (161 : ℝ) ^ 2 + 26 / (10 * 12464) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12464) : ℝ)) (tA 12464 * 161 ^ 2 + 26 / (10 * 12464)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3693139 / 1000000000))) * ((126033849 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3693139 / 1000000000)) ^ 3) * ((1617892821 / 1000000000000000000000000))) + ((5949127261 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3693139 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12464) : ℝ)) d.D d.V d.P (√(tA 12464) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3693139 / 1000000000)) ^ 2 * (((2245295963 / 1000000000000000)) * ((10055759609 / 250000000000000000)))) + ((5949127261 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12464) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3693139 / 1000000000)) * ((126033849 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12464) : ℝ)) (tA 12464 * 161 ^ 2 + 26 / (10 * 12464)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((126033849 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3693139 / 1000000000)) ^ 2) * ((1617892821 / 1000000000000000000000000)) + ((5949127261 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12464) : ℝ)) (√(26 / (10 * 12464) : ℝ)) d.D d.V d.P (√(tA 12464) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3693139 / 1000000000)) * (((2245295963 / 1000000000000000)) * ((10055759609 / 250000000000000000))) + ((5949127261 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12464) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((126033849 / 25000000000000000000) : ℝ) + ((5949127261 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12464

namespace BstLean.Part266.Row12464
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12464 161 ∧
    0 ≤ (tableEnvelope C).f1 12464 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12464 161 ∧
    0 ≤ (tableEnvelope C).w1 12464 161 ∧ 0 ≤ (tableEnvelope C).w2 12464 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12464 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12464 161 ∧ 0 ≤ d.f1 12464 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12464 161 ∧ 0 ≤ d.w1 12464 161 ∧ 0 ≤ d.w2 12464 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12464 ≤ 2 * (228 / 100 : ℝ) / 12464 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12464 ≤ 2 * (370 / 100 : ℝ) / 12464 := by
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
    (completeRAData (tableEnvelope C) 12464 161).locationBound 12464 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12464 161).energyBound 12464 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12464 161) (d.f1 12464 161) d.f2 ≤
      32 * (((4802736223 / 1000000000000000000) : ℝ) + (160227407 / 100000000000000000) + (96276781 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12464 161) (d.w1 12464 161)
      (d.w2 12464 161) ≤
      32 * (((1939321831 / 100000000000000000000) : ℝ) + (689895193 / 50000000000000000000) + (504141159 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12464 161) (d.f1 12464 161) d.f2 ≤
      ((4802736223 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4802736223 / 1000000000000000000)) * ((160227407 / 100000000000000000)) * (126 / 100) +
      2 * (((160227407 / 100000000000000000)) ^ 2 + 2 * ((4802736223 / 1000000000000000000)) * ((96276781 / 250000000000000000))) +
      6 * ((160227407 / 100000000000000000)) * ((96276781 / 250000000000000000)) * (126 / 100) + 8 * ((96276781 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12464 161) (d.f1 12464 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12464 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12464 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12464 161) (d.f1 12464 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12464 161) (d.w1 12464 161) (d.w2 12464 161)
  have hwexpr0 : 0 ≤ d.w0 12464 161 + d.w1 12464 161 * √(π / 2) +
      2 * d.w2 12464 161 + energyR16 12464 *
      radiusPolynomialRoot16 (d.w0 12464 161) (d.w1 12464 161) (d.w2 12464 161) := by
    positivity
  constructor
  · change (12464 : ℝ) ^ 8 * (mA 12464 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12464 161) (d.f1 12464 161) d.f2 + locationR16 12464 *
        radiusPolynomialRoot16 (d.f0 12464 161) (d.f1 12464 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12464 : ℝ) ^ 8 * (mA 12464 : ℝ) ^ 8 *
        ((((4802736223 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4802736223 / 1000000000000000000)) * ((160227407 / 100000000000000000)) * (126 / 100) +
          2 * (((160227407 / 100000000000000000)) ^ 2 + 2 * ((4802736223 / 1000000000000000000)) * ((96276781 / 250000000000000000))) +
          6 * ((160227407 / 100000000000000000)) * ((96276781 / 250000000000000000)) * (126 / 100) + 8 * ((96276781 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12464) *
          (32 * (((4802736223 / 1000000000000000000) : ℝ) + (160227407 / 100000000000000000) + (96276781 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12464 : ℝ) ^ 16 *
      (d.w0 12464 161 + d.w1 12464 161 * √(π / 2) + 2 * d.w2 12464 161 +
        energyR16 12464 * radiusPolynomialRoot16 (d.w0 12464 161) (d.w1 12464 161)
          (d.w2 12464 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12464 : ℝ) ^ 16 *
        (((1939321831 / 100000000000000000000) : ℝ) + ((689895193 / 50000000000000000000)) * (126 / 100) + 2 * ((504141159 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12464) *
          (32 * (((1939321831 / 100000000000000000000) : ℝ) + (689895193 / 50000000000000000000) + (504141159 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12464

/-! A coarse bound on the actual paper statistics constant at dimension 12465. -/
namespace BstLean.Part266.Row12465
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12463 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12463 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12463 128 ≤ (12717 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12717 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12465) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12465 : ℕ))
    (by norm_num : (12465 : ℕ) ≤ 16384)
  have ht : paperTail256 12465 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12465 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12465 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12465 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12465 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12465 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12463 128 * √(2 / (12465 : ℝ)) *
      (√(12465 : ℝ) + paperT0 12465 + paperTail256 12465) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12465 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12465 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12465 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12463 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12463 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12465 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12465

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12465
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12465 (61 / 100) 161 (17 / (100 * 12465)) (26 / (10 * 12465)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12465 (61 / 100) 161 (17 / (100 * 12465)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (504014067 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (404343421 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5945272547 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12465 / 12465 * (61 / 100)) ^ 4 * inverseRadius8 (12465 - 1) /
            envelopeGap 12465 (61 / 100) 161 (17 / (100 * 12465)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12465

namespace BstLean.Part266.Row12465
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12465 161 ≤ (2400886219 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12465 161 ≤ (160195259 / 100000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (385029871 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12465 161 ≤ (484713747 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12465 161 ≤ (1379458261 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12465 161 ≤ (504019827 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (504014067 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (504014067 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (404343421 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5945272547 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3692991 / 1000000000) : ℝ) ≤ √(17 / (100 * 12465) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12465) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1122512881 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40216584689 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12465) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12465) ≤ (113454759 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12465) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12465 * (161 : ℝ) ^ 2 + 26 / (10 * 12465) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12465) : ℝ)) (tA 12465 * 161 ^ 2 + 26 / (10 * 12465)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3692991 / 1000000000))) * ((504014067 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3692991 / 1000000000)) ^ 3) * ((404343421 / 250000000000000000000000))) + ((5945272547 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3692991 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12465) : ℝ)) d.D d.V d.P (√(tA 12465) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3692991 / 1000000000)) ^ 2 * (((1122512881 / 500000000000000)) * ((40216584689 / 1000000000000000000)))) + ((5945272547 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12465) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3692991 / 1000000000)) * ((504014067 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12465) : ℝ)) (tA 12465 * 161 ^ 2 + 26 / (10 * 12465)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((504014067 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3692991 / 1000000000)) ^ 2) * ((404343421 / 250000000000000000000000)) + ((5945272547 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12465) : ℝ)) (√(26 / (10 * 12465) : ℝ)) d.D d.V d.P (√(tA 12465) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3692991 / 1000000000)) * (((1122512881 / 500000000000000)) * ((40216584689 / 1000000000000000000))) + ((5945272547 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12465) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((504014067 / 100000000000000000000) : ℝ) + ((5945272547 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12465

namespace BstLean.Part266.Row12465
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12465 161 ∧
    0 ≤ (tableEnvelope C).f1 12465 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12465 161 ∧
    0 ≤ (tableEnvelope C).w1 12465 161 ∧ 0 ≤ (tableEnvelope C).w2 12465 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12465 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12465 161 ∧ 0 ≤ d.f1 12465 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12465 161 ∧ 0 ≤ d.w1 12465 161 ∧ 0 ≤ d.w2 12465 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12465 ≤ 2 * (228 / 100 : ℝ) / 12465 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12465 ≤ 2 * (370 / 100 : ℝ) / 12465 := by
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
    (completeRAData (tableEnvelope C) 12465 161).locationBound 12465 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12465 161).energyBound 12465 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12465 161) (d.f1 12465 161) d.f2 ≤
      32 * (((2400886219 / 500000000000000000) : ℝ) + (160195259 / 100000000000000000) + (385029871 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12465 161) (d.w1 12465 161)
      (d.w2 12465 161) ≤
      32 * (((484713747 / 25000000000000000000) : ℝ) + (1379458261 / 100000000000000000000) + (504019827 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12465 161) (d.f1 12465 161) d.f2 ≤
      ((2400886219 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2400886219 / 500000000000000000)) * ((160195259 / 100000000000000000)) * (126 / 100) +
      2 * (((160195259 / 100000000000000000)) ^ 2 + 2 * ((2400886219 / 500000000000000000)) * ((385029871 / 1000000000000000000))) +
      6 * ((160195259 / 100000000000000000)) * ((385029871 / 1000000000000000000)) * (126 / 100) + 8 * ((385029871 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12465 161) (d.f1 12465 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12465 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12465 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12465 161) (d.f1 12465 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12465 161) (d.w1 12465 161) (d.w2 12465 161)
  have hwexpr0 : 0 ≤ d.w0 12465 161 + d.w1 12465 161 * √(π / 2) +
      2 * d.w2 12465 161 + energyR16 12465 *
      radiusPolynomialRoot16 (d.w0 12465 161) (d.w1 12465 161) (d.w2 12465 161) := by
    positivity
  constructor
  · change (12465 : ℝ) ^ 8 * (mA 12465 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12465 161) (d.f1 12465 161) d.f2 + locationR16 12465 *
        radiusPolynomialRoot16 (d.f0 12465 161) (d.f1 12465 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12465 : ℝ) ^ 8 * (mA 12465 : ℝ) ^ 8 *
        ((((2400886219 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2400886219 / 500000000000000000)) * ((160195259 / 100000000000000000)) * (126 / 100) +
          2 * (((160195259 / 100000000000000000)) ^ 2 + 2 * ((2400886219 / 500000000000000000)) * ((385029871 / 1000000000000000000))) +
          6 * ((160195259 / 100000000000000000)) * ((385029871 / 1000000000000000000)) * (126 / 100) + 8 * ((385029871 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12465) *
          (32 * (((2400886219 / 500000000000000000) : ℝ) + (160195259 / 100000000000000000) + (385029871 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12465 : ℝ) ^ 16 *
      (d.w0 12465 161 + d.w1 12465 161 * √(π / 2) + 2 * d.w2 12465 161 +
        energyR16 12465 * radiusPolynomialRoot16 (d.w0 12465 161) (d.w1 12465 161)
          (d.w2 12465 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12465 : ℝ) ^ 16 *
        (((484713747 / 25000000000000000000) : ℝ) + ((1379458261 / 100000000000000000000)) * (126 / 100) + 2 * ((504019827 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12465) *
          (32 * (((484713747 / 25000000000000000000) : ℝ) + (1379458261 / 100000000000000000000) + (504019827 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12465

/-! A coarse bound on the actual paper statistics constant at dimension 12466. -/
namespace BstLean.Part266.Row12466
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12464 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12464 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12464 128 ≤ (12718 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12718 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12466) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12466 : ℕ))
    (by norm_num : (12466 : ℕ) ≤ 16384)
  have ht : paperTail256 12466 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12466 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12466 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12466 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12466 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12466 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12464 128 * √(2 / (12466 : ℝ)) *
      (√(12466 : ℝ) + paperT0 12466 + paperTail256 12466) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12466 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12466 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12466 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12464 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12464 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12466 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12466

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12466
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12466 (61 / 100) 161 (17 / (100 * 12466)) (26 / (10 * 12466)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12466 (61 / 100) 161 (17 / (100 * 12466)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (503892777 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (808427377 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1188284129 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12466 / 12466 * (61 / 100)) ^ 4 * inverseRadius8 (12466 - 1) /
            envelopeGap 12466 (61 / 100) 161 (17 / (100 * 12466)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12466

namespace BstLean.Part266.Row12466
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12466 161 ≤ (1200202247 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12466 161 ≤ (320326243 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (192476321 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12466 161 ≤ (1938388307 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12466 161 ≤ (1103301 / 80000000000000000)
  w2 : (tableEnvelope C).w2 12466 161 ≤ (503898533 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (503892777 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (503892777 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (808427377 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1188284129 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3692843 / 1000000000) : ℝ) ≤ √(17 / (100 * 12466) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12466) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (448951123 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (15707083 / 390625000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12466) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12466) ≤ (56722829 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12466) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12466 * (161 : ℝ) ^ 2 + 26 / (10 * 12466) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12466) : ℝ)) (tA 12466 * 161 ^ 2 + 26 / (10 * 12466)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3692843 / 1000000000))) * ((503892777 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3692843 / 1000000000)) ^ 3) * ((808427377 / 500000000000000000000000))) + ((1188284129 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3692843 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12466) : ℝ)) d.D d.V d.P (√(tA 12466) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3692843 / 1000000000)) ^ 2 * (((448951123 / 200000000000000)) * ((15707083 / 390625000000000)))) + ((1188284129 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12466) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3692843 / 1000000000)) * ((503892777 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12466) : ℝ)) (tA 12466 * 161 ^ 2 + 26 / (10 * 12466)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((503892777 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3692843 / 1000000000)) ^ 2) * ((808427377 / 500000000000000000000000)) + ((1188284129 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12466) : ℝ)) (√(26 / (10 * 12466) : ℝ)) d.D d.V d.P (√(tA 12466) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3692843 / 1000000000)) * (((448951123 / 200000000000000)) * ((15707083 / 390625000000000))) + ((1188284129 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12466) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((503892777 / 100000000000000000000) : ℝ) + ((1188284129 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12466

namespace BstLean.Part266.Row12466
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12466 161 ∧
    0 ≤ (tableEnvelope C).f1 12466 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12466 161 ∧
    0 ≤ (tableEnvelope C).w1 12466 161 ∧ 0 ≤ (tableEnvelope C).w2 12466 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12466 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12466 161 ∧ 0 ≤ d.f1 12466 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12466 161 ∧ 0 ≤ d.w1 12466 161 ∧ 0 ≤ d.w2 12466 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12466 ≤ 2 * (228 / 100 : ℝ) / 12466 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12466 ≤ 2 * (370 / 100 : ℝ) / 12466 := by
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
    (completeRAData (tableEnvelope C) 12466 161).locationBound 12466 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12466 161).energyBound 12466 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12466 161) (d.f1 12466 161) d.f2 ≤
      32 * (((1200202247 / 250000000000000000) : ℝ) + (320326243 / 200000000000000000) + (192476321 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12466 161) (d.w1 12466 161)
      (d.w2 12466 161) ≤
      32 * (((1938388307 / 100000000000000000000) : ℝ) + (1103301 / 80000000000000000) + (503898533 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12466 161) (d.f1 12466 161) d.f2 ≤
      ((1200202247 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1200202247 / 250000000000000000)) * ((320326243 / 200000000000000000)) * (126 / 100) +
      2 * (((320326243 / 200000000000000000)) ^ 2 + 2 * ((1200202247 / 250000000000000000)) * ((192476321 / 500000000000000000))) +
      6 * ((320326243 / 200000000000000000)) * ((192476321 / 500000000000000000)) * (126 / 100) + 8 * ((192476321 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12466 161) (d.f1 12466 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12466 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12466 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12466 161) (d.f1 12466 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12466 161) (d.w1 12466 161) (d.w2 12466 161)
  have hwexpr0 : 0 ≤ d.w0 12466 161 + d.w1 12466 161 * √(π / 2) +
      2 * d.w2 12466 161 + energyR16 12466 *
      radiusPolynomialRoot16 (d.w0 12466 161) (d.w1 12466 161) (d.w2 12466 161) := by
    positivity
  constructor
  · change (12466 : ℝ) ^ 8 * (mA 12466 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12466 161) (d.f1 12466 161) d.f2 + locationR16 12466 *
        radiusPolynomialRoot16 (d.f0 12466 161) (d.f1 12466 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12466 : ℝ) ^ 8 * (mA 12466 : ℝ) ^ 8 *
        ((((1200202247 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1200202247 / 250000000000000000)) * ((320326243 / 200000000000000000)) * (126 / 100) +
          2 * (((320326243 / 200000000000000000)) ^ 2 + 2 * ((1200202247 / 250000000000000000)) * ((192476321 / 500000000000000000))) +
          6 * ((320326243 / 200000000000000000)) * ((192476321 / 500000000000000000)) * (126 / 100) + 8 * ((192476321 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12466) *
          (32 * (((1200202247 / 250000000000000000) : ℝ) + (320326243 / 200000000000000000) + (192476321 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12466 : ℝ) ^ 16 *
      (d.w0 12466 161 + d.w1 12466 161 * √(π / 2) + 2 * d.w2 12466 161 +
        energyR16 12466 * radiusPolynomialRoot16 (d.w0 12466 161) (d.w1 12466 161)
          (d.w2 12466 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12466 : ℝ) ^ 16 *
        (((1938388307 / 100000000000000000000) : ℝ) + ((1103301 / 80000000000000000)) * (126 / 100) + 2 * ((503898533 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12466) *
          (32 * (((1938388307 / 100000000000000000000) : ℝ) + (1103301 / 80000000000000000) + (503898533 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12466

/-! A coarse bound on the actual paper statistics constant at dimension 12467. -/
namespace BstLean.Part266.Row12467
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12465 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12465 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12465 128 ≤ (12719 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12719 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12467) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12467 : ℕ))
    (by norm_num : (12467 : ℕ) ≤ 16384)
  have ht : paperTail256 12467 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12467 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12467 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12467 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12467 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12467 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12465 128 * √(2 / (12467 : ℝ)) *
      (√(12467 : ℝ) + paperT0 12467 + paperTail256 12467) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12467 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12467 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12467 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12465 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12465 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12467 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12467

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12467
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12467 (61 / 100) 161 (17 / (100 * 12467)) (26 / (10 * 12467)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12467 (61 / 100) 161 (17 / (100 * 12467)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (20150861 / 4000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1616336033 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2968785777 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12467 / 12467 * (61 / 100)) ^ 4 * inverseRadius8 (12467 - 1) /
            envelopeGap 12467 (61 / 100) 161 (17 / (100 * 12467)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12467

namespace BstLean.Part266.Row12467
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12467 161 ≤ (2399922939 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12467 161 ≤ (320261989 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (76975087 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12467 161 ≤ (1937921791 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12467 161 ≤ (1378794351 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12467 161 ≤ (503777277 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (20150861 / 4000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (20150861 / 4000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1616336033 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2968785777 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((738539 / 200000000) : ℝ) ≤ √(17 / (100 * 12467) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12467) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2244485521 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (20101840917 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12467) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12467) ≤ (56718279 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12467) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12467 * (161 : ℝ) ^ 2 + 26 / (10 * 12467) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12467) : ℝ)) (tA 12467 * 161 ^ 2 + 26 / (10 * 12467)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((738539 / 200000000))) * ((20150861 / 4000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((738539 / 200000000)) ^ 3) * ((1616336033 / 1000000000000000000000000))) + ((2968785777 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((738539 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12467) : ℝ)) d.D d.V d.P (√(tA 12467) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((738539 / 200000000)) ^ 2 * (((2244485521 / 1000000000000000)) * ((20101840917 / 500000000000000000)))) + ((2968785777 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12467) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((738539 / 200000000)) * ((20150861 / 4000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12467) : ℝ)) (tA 12467 * 161 ^ 2 + 26 / (10 * 12467)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((20150861 / 4000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((738539 / 200000000)) ^ 2) * ((1616336033 / 1000000000000000000000000)) + ((2968785777 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12467) : ℝ)) (√(26 / (10 * 12467) : ℝ)) d.D d.V d.P (√(tA 12467) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((738539 / 200000000)) * (((2244485521 / 1000000000000000)) * ((20101840917 / 500000000000000000))) + ((2968785777 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12467) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((20150861 / 4000000000000000000) : ℝ) + ((2968785777 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12467

namespace BstLean.Part266.Row12467
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12467 161 ∧
    0 ≤ (tableEnvelope C).f1 12467 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12467 161 ∧
    0 ≤ (tableEnvelope C).w1 12467 161 ∧ 0 ≤ (tableEnvelope C).w2 12467 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12467 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12467 161 ∧ 0 ≤ d.f1 12467 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12467 161 ∧ 0 ≤ d.w1 12467 161 ∧ 0 ≤ d.w2 12467 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12467 ≤ 2 * (228 / 100 : ℝ) / 12467 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12467 ≤ 2 * (370 / 100 : ℝ) / 12467 := by
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
    (completeRAData (tableEnvelope C) 12467 161).locationBound 12467 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12467 161).energyBound 12467 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12467 161) (d.f1 12467 161) d.f2 ≤
      32 * (((2399922939 / 500000000000000000) : ℝ) + (320261989 / 200000000000000000) + (76975087 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12467 161) (d.w1 12467 161)
      (d.w2 12467 161) ≤
      32 * (((1937921791 / 100000000000000000000) : ℝ) + (1378794351 / 100000000000000000000) + (503777277 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12467 161) (d.f1 12467 161) d.f2 ≤
      ((2399922939 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2399922939 / 500000000000000000)) * ((320261989 / 200000000000000000)) * (126 / 100) +
      2 * (((320261989 / 200000000000000000)) ^ 2 + 2 * ((2399922939 / 500000000000000000)) * ((76975087 / 200000000000000000))) +
      6 * ((320261989 / 200000000000000000)) * ((76975087 / 200000000000000000)) * (126 / 100) + 8 * ((76975087 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12467 161) (d.f1 12467 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12467 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12467 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12467 161) (d.f1 12467 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12467 161) (d.w1 12467 161) (d.w2 12467 161)
  have hwexpr0 : 0 ≤ d.w0 12467 161 + d.w1 12467 161 * √(π / 2) +
      2 * d.w2 12467 161 + energyR16 12467 *
      radiusPolynomialRoot16 (d.w0 12467 161) (d.w1 12467 161) (d.w2 12467 161) := by
    positivity
  constructor
  · change (12467 : ℝ) ^ 8 * (mA 12467 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12467 161) (d.f1 12467 161) d.f2 + locationR16 12467 *
        radiusPolynomialRoot16 (d.f0 12467 161) (d.f1 12467 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12467 : ℝ) ^ 8 * (mA 12467 : ℝ) ^ 8 *
        ((((2399922939 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2399922939 / 500000000000000000)) * ((320261989 / 200000000000000000)) * (126 / 100) +
          2 * (((320261989 / 200000000000000000)) ^ 2 + 2 * ((2399922939 / 500000000000000000)) * ((76975087 / 200000000000000000))) +
          6 * ((320261989 / 200000000000000000)) * ((76975087 / 200000000000000000)) * (126 / 100) + 8 * ((76975087 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12467) *
          (32 * (((2399922939 / 500000000000000000) : ℝ) + (320261989 / 200000000000000000) + (76975087 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12467 : ℝ) ^ 16 *
      (d.w0 12467 161 + d.w1 12467 161 * √(π / 2) + 2 * d.w2 12467 161 +
        energyR16 12467 * radiusPolynomialRoot16 (d.w0 12467 161) (d.w1 12467 161)
          (d.w2 12467 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12467 : ℝ) ^ 16 *
        (((1937921791 / 100000000000000000000) : ℝ) + ((1378794351 / 100000000000000000000)) * (126 / 100) + 2 * ((503777277 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12467) *
          (32 * (((1937921791 / 100000000000000000000) : ℝ) + (1378794351 / 100000000000000000000) + (503777277 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12467

/-! A coarse bound on the actual paper statistics constant at dimension 12468. -/
namespace BstLean.Part266.Row12468
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12466 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12466 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12466 128 ≤ (12720 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12720 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12468) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12468 : ℕ))
    (by norm_num : (12468 : ℕ) ≤ 16384)
  have ht : paperTail256 12468 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12468 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12468 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12468 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12468 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12468 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12466 128 * √(2 / (12468 : ℝ)) *
      (√(12468 : ℝ) + paperT0 12468 + paperTail256 12468) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12468 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12468 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12468 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12466 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12466 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12468 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12468

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12468
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12468 (61 / 100) 161 (17 / (100 * 12468)) (26 / (10 * 12468)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12468 (61 / 100) 161 (17 / (100 * 12468)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (503650313 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1615817519 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (593372527 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12468 / 12468 * (61 / 100)) ^ 4 * inverseRadius8 (12468 - 1) /
            envelopeGap 12468 (61 / 100) 161 (17 / (100 * 12468)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12468

namespace BstLean.Part266.Row12468
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12468 161 ≤ (2399441551 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12468 161 ≤ (1600988781 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (384798253 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12468 161 ≤ (968727719 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12468 161 ≤ (689231283 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12468 161 ≤ (503656061 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (503650313 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (503650313 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1615817519 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (593372527 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3692547 / 1000000000) : ℝ) ≤ √(17 / (100 * 12468) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12468) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2244215483 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40197232729 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12468) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12468) ≤ (5671373 / 50000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12468) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12468 * (161 : ℝ) ^ 2 + 26 / (10 * 12468) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12468) : ℝ)) (tA 12468 * 161 ^ 2 + 26 / (10 * 12468)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3692547 / 1000000000))) * ((503650313 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3692547 / 1000000000)) ^ 3) * ((1615817519 / 1000000000000000000000000))) + ((593372527 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3692547 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12468) : ℝ)) d.D d.V d.P (√(tA 12468) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3692547 / 1000000000)) ^ 2 * (((2244215483 / 1000000000000000)) * ((40197232729 / 1000000000000000000)))) + ((593372527 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12468) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3692547 / 1000000000)) * ((503650313 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12468) : ℝ)) (tA 12468 * 161 ^ 2 + 26 / (10 * 12468)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((503650313 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3692547 / 1000000000)) ^ 2) * ((1615817519 / 1000000000000000000000000)) + ((593372527 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12468) : ℝ)) (√(26 / (10 * 12468) : ℝ)) d.D d.V d.P (√(tA 12468) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3692547 / 1000000000)) * (((2244215483 / 1000000000000000)) * ((40197232729 / 1000000000000000000))) + ((593372527 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12468) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((503650313 / 100000000000000000000) : ℝ) + ((593372527 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12468

namespace BstLean.Part266.Row12468
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12468 161 ∧
    0 ≤ (tableEnvelope C).f1 12468 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12468 161 ∧
    0 ≤ (tableEnvelope C).w1 12468 161 ∧ 0 ≤ (tableEnvelope C).w2 12468 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12468 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12468 161 ∧ 0 ≤ d.f1 12468 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12468 161 ∧ 0 ≤ d.w1 12468 161 ∧ 0 ≤ d.w2 12468 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12468 ≤ 2 * (228 / 100 : ℝ) / 12468 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12468 ≤ 2 * (370 / 100 : ℝ) / 12468 := by
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
    (completeRAData (tableEnvelope C) 12468 161).locationBound 12468 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12468 161).energyBound 12468 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12468 161) (d.f1 12468 161) d.f2 ≤
      32 * (((2399441551 / 500000000000000000) : ℝ) + (1600988781 / 1000000000000000000) + (384798253 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12468 161) (d.w1 12468 161)
      (d.w2 12468 161) ≤
      32 * (((968727719 / 50000000000000000000) : ℝ) + (689231283 / 50000000000000000000) + (503656061 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12468 161) (d.f1 12468 161) d.f2 ≤
      ((2399441551 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2399441551 / 500000000000000000)) * ((1600988781 / 1000000000000000000)) * (126 / 100) +
      2 * (((1600988781 / 1000000000000000000)) ^ 2 + 2 * ((2399441551 / 500000000000000000)) * ((384798253 / 1000000000000000000))) +
      6 * ((1600988781 / 1000000000000000000)) * ((384798253 / 1000000000000000000)) * (126 / 100) + 8 * ((384798253 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12468 161) (d.f1 12468 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12468 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12468 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12468 161) (d.f1 12468 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12468 161) (d.w1 12468 161) (d.w2 12468 161)
  have hwexpr0 : 0 ≤ d.w0 12468 161 + d.w1 12468 161 * √(π / 2) +
      2 * d.w2 12468 161 + energyR16 12468 *
      radiusPolynomialRoot16 (d.w0 12468 161) (d.w1 12468 161) (d.w2 12468 161) := by
    positivity
  constructor
  · change (12468 : ℝ) ^ 8 * (mA 12468 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12468 161) (d.f1 12468 161) d.f2 + locationR16 12468 *
        radiusPolynomialRoot16 (d.f0 12468 161) (d.f1 12468 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12468 : ℝ) ^ 8 * (mA 12468 : ℝ) ^ 8 *
        ((((2399441551 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2399441551 / 500000000000000000)) * ((1600988781 / 1000000000000000000)) * (126 / 100) +
          2 * (((1600988781 / 1000000000000000000)) ^ 2 + 2 * ((2399441551 / 500000000000000000)) * ((384798253 / 1000000000000000000))) +
          6 * ((1600988781 / 1000000000000000000)) * ((384798253 / 1000000000000000000)) * (126 / 100) + 8 * ((384798253 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12468) *
          (32 * (((2399441551 / 500000000000000000) : ℝ) + (1600988781 / 1000000000000000000) + (384798253 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12468 : ℝ) ^ 16 *
      (d.w0 12468 161 + d.w1 12468 161 * √(π / 2) + 2 * d.w2 12468 161 +
        energyR16 12468 * radiusPolynomialRoot16 (d.w0 12468 161) (d.w1 12468 161)
          (d.w2 12468 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12468 : ℝ) ^ 16 *
        (((968727719 / 50000000000000000000) : ℝ) + ((689231283 / 50000000000000000000)) * (126 / 100) + 2 * ((503656061 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12468) *
          (32 * (((968727719 / 50000000000000000000) : ℝ) + (689231283 / 50000000000000000000) + (503656061 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12468

/-! A coarse bound on the actual paper statistics constant at dimension 12469. -/
namespace BstLean.Part266.Row12469
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12467 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12467 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12467 128 ≤ (12721 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12721 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12469) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12469 : ℕ))
    (by norm_num : (12469 : ℕ) ≤ 16384)
  have ht : paperTail256 12469 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12469 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12469 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12469 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12469 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12469 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12467 128 * √(2 / (12469 : ℝ)) *
      (√(12469 : ℝ) + paperT0 12469 + paperTail256 12469) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12469 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12469 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12469 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12467 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12467 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12469 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12469

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12469
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12469 (61 / 100) 161 (17 / (100 * 12469)) (26 / (10 * 12469)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12469 (61 / 100) 161 (17 / (100 * 12469)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (25176457 / 5000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (807649607 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5929881793 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12469 / 12469 * (61 / 100)) ^ 4 * inverseRadius8 (12469 - 1) /
            envelopeGap 12469 (61 / 100) 161 (17 / (100 * 12469)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12469

namespace BstLean.Part266.Row12469
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12469 161 ≤ (2398960333 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12469 161 ≤ (400166931 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (76944219 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12469 161 ≤ (1936989249 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12469 161 ≤ (275626179 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12469 161 ≤ (100706977 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (25176457 / 5000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (25176457 / 5000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (807649607 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5929881793 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3692399 / 1000000000) : ℝ) ≤ √(17 / (100 * 12469) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12469) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2243945499 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (10047696297 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12469) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12469) ≤ (113418363 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12469) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12469 * (161 : ℝ) ^ 2 + 26 / (10 * 12469) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12469) : ℝ)) (tA 12469 * 161 ^ 2 + 26 / (10 * 12469)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3692399 / 1000000000))) * ((25176457 / 5000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3692399 / 1000000000)) ^ 3) * ((807649607 / 500000000000000000000000))) + ((5929881793 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3692399 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12469) : ℝ)) d.D d.V d.P (√(tA 12469) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3692399 / 1000000000)) ^ 2 * (((2243945499 / 1000000000000000)) * ((10047696297 / 250000000000000000)))) + ((5929881793 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12469) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3692399 / 1000000000)) * ((25176457 / 5000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12469) : ℝ)) (tA 12469 * 161 ^ 2 + 26 / (10 * 12469)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((25176457 / 5000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3692399 / 1000000000)) ^ 2) * ((807649607 / 500000000000000000000000)) + ((5929881793 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12469) : ℝ)) (√(26 / (10 * 12469) : ℝ)) d.D d.V d.P (√(tA 12469) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3692399 / 1000000000)) * (((2243945499 / 1000000000000000)) * ((10047696297 / 250000000000000000))) + ((5929881793 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12469) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((25176457 / 5000000000000000000) : ℝ) + ((5929881793 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12469

namespace BstLean.Part266.Row12469
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12469 161 ∧
    0 ≤ (tableEnvelope C).f1 12469 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12469 161 ∧
    0 ≤ (tableEnvelope C).w1 12469 161 ∧ 0 ≤ (tableEnvelope C).w2 12469 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12469 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12469 161 ∧ 0 ≤ d.f1 12469 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12469 161 ∧ 0 ≤ d.w1 12469 161 ∧ 0 ≤ d.w2 12469 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12469 ≤ 2 * (228 / 100 : ℝ) / 12469 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12469 ≤ 2 * (370 / 100 : ℝ) / 12469 := by
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
    (completeRAData (tableEnvelope C) 12469 161).locationBound 12469 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12469 161).energyBound 12469 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12469 161) (d.f1 12469 161) d.f2 ≤
      32 * (((2398960333 / 500000000000000000) : ℝ) + (400166931 / 250000000000000000) + (76944219 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12469 161) (d.w1 12469 161)
      (d.w2 12469 161) ≤
      32 * (((1936989249 / 100000000000000000000) : ℝ) + (275626179 / 20000000000000000000) + (100706977 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12469 161) (d.f1 12469 161) d.f2 ≤
      ((2398960333 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2398960333 / 500000000000000000)) * ((400166931 / 250000000000000000)) * (126 / 100) +
      2 * (((400166931 / 250000000000000000)) ^ 2 + 2 * ((2398960333 / 500000000000000000)) * ((76944219 / 200000000000000000))) +
      6 * ((400166931 / 250000000000000000)) * ((76944219 / 200000000000000000)) * (126 / 100) + 8 * ((76944219 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12469 161) (d.f1 12469 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12469 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12469 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12469 161) (d.f1 12469 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12469 161) (d.w1 12469 161) (d.w2 12469 161)
  have hwexpr0 : 0 ≤ d.w0 12469 161 + d.w1 12469 161 * √(π / 2) +
      2 * d.w2 12469 161 + energyR16 12469 *
      radiusPolynomialRoot16 (d.w0 12469 161) (d.w1 12469 161) (d.w2 12469 161) := by
    positivity
  constructor
  · change (12469 : ℝ) ^ 8 * (mA 12469 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12469 161) (d.f1 12469 161) d.f2 + locationR16 12469 *
        radiusPolynomialRoot16 (d.f0 12469 161) (d.f1 12469 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12469 : ℝ) ^ 8 * (mA 12469 : ℝ) ^ 8 *
        ((((2398960333 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2398960333 / 500000000000000000)) * ((400166931 / 250000000000000000)) * (126 / 100) +
          2 * (((400166931 / 250000000000000000)) ^ 2 + 2 * ((2398960333 / 500000000000000000)) * ((76944219 / 200000000000000000))) +
          6 * ((400166931 / 250000000000000000)) * ((76944219 / 200000000000000000)) * (126 / 100) + 8 * ((76944219 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12469) *
          (32 * (((2398960333 / 500000000000000000) : ℝ) + (400166931 / 250000000000000000) + (76944219 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12469 : ℝ) ^ 16 *
      (d.w0 12469 161 + d.w1 12469 161 * √(π / 2) + 2 * d.w2 12469 161 +
        energyR16 12469 * radiusPolynomialRoot16 (d.w0 12469 161) (d.w1 12469 161)
          (d.w2 12469 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12469 : ℝ) ^ 16 *
        (((1936989249 / 100000000000000000000) : ℝ) + ((275626179 / 20000000000000000000)) * (126 / 100) + 2 * ((100706977 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12469) *
          (32 * (((1936989249 / 100000000000000000000) : ℝ) + (275626179 / 20000000000000000000) + (100706977 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12469

/-! A coarse bound on the actual paper statistics constant at dimension 12470. -/
namespace BstLean.Part266.Row12470
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12468 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12468 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12468 128 ≤ (12722 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12722 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12470) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12470 : ℕ))
    (by norm_num : (12470 : ℕ) ≤ 16384)
  have ht : paperTail256 12470 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12470 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12470 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12470 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12470 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12470 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12468 128 * √(2 / (12470 : ℝ)) *
      (√(12470 : ℝ) + paperT0 12470 + paperTail256 12470) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12470 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12470 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12470 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12468 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12468 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12470 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12470

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12470
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12470 (61 / 100) 161 (17 / (100 * 12470)) (26 / (10 * 12470)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12470 (61 / 100) 161 (17 / (100 * 12470)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (100681601 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (403695279 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2963020559 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12470 / 12470 * (61 / 100)) ^ 4 * inverseRadius8 (12470 - 1) /
            envelopeGap 12470 (61 / 100) 161 (17 / (100 * 12470)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12470

namespace BstLean.Part266.Row12470
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12470 161 ≤ (959391713 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12470 161 ≤ (1600346771 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (384643959 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12470 161 ≤ (968261611 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12470 161 ≤ (275559867 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12470 161 ≤ (251706873 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (100681601 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (100681601 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (403695279 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2963020559 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3692251 / 1000000000) : ℝ) ≤ √(17 / (100 * 12470) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12470) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (140229723 / 62500000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40184339189 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12470) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12470) ≤ (28352317 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12470) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12470 * (161 : ℝ) ^ 2 + 26 / (10 * 12470) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12470) : ℝ)) (tA 12470 * 161 ^ 2 + 26 / (10 * 12470)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3692251 / 1000000000))) * ((100681601 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3692251 / 1000000000)) ^ 3) * ((403695279 / 250000000000000000000000))) + ((2963020559 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3692251 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12470) : ℝ)) d.D d.V d.P (√(tA 12470) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3692251 / 1000000000)) ^ 2 * (((140229723 / 62500000000000)) * ((40184339189 / 1000000000000000000)))) + ((2963020559 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12470) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3692251 / 1000000000)) * ((100681601 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12470) : ℝ)) (tA 12470 * 161 ^ 2 + 26 / (10 * 12470)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((100681601 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3692251 / 1000000000)) ^ 2) * ((403695279 / 250000000000000000000000)) + ((2963020559 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12470) : ℝ)) (√(26 / (10 * 12470) : ℝ)) d.D d.V d.P (√(tA 12470) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3692251 / 1000000000)) * (((140229723 / 62500000000000)) * ((40184339189 / 1000000000000000000))) + ((2963020559 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12470) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((100681601 / 20000000000000000000) : ℝ) + ((2963020559 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12470

namespace BstLean.Part266.Row12470
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12470 161 ∧
    0 ≤ (tableEnvelope C).f1 12470 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12470 161 ∧
    0 ≤ (tableEnvelope C).w1 12470 161 ∧ 0 ≤ (tableEnvelope C).w2 12470 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12470 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12470 161 ∧ 0 ≤ d.f1 12470 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12470 161 ∧ 0 ≤ d.w1 12470 161 ∧ 0 ≤ d.w2 12470 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12470 ≤ 2 * (228 / 100 : ℝ) / 12470 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12470 ≤ 2 * (370 / 100 : ℝ) / 12470 := by
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
    (completeRAData (tableEnvelope C) 12470 161).locationBound 12470 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12470 161).energyBound 12470 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12470 161) (d.f1 12470 161) d.f2 ≤
      32 * (((959391713 / 200000000000000000) : ℝ) + (1600346771 / 1000000000000000000) + (384643959 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12470 161) (d.w1 12470 161)
      (d.w2 12470 161) ≤
      32 * (((968261611 / 50000000000000000000) : ℝ) + (275559867 / 20000000000000000000) + (251706873 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12470 161) (d.f1 12470 161) d.f2 ≤
      ((959391713 / 200000000000000000) : ℝ) ^ 2 + 2 * ((959391713 / 200000000000000000)) * ((1600346771 / 1000000000000000000)) * (126 / 100) +
      2 * (((1600346771 / 1000000000000000000)) ^ 2 + 2 * ((959391713 / 200000000000000000)) * ((384643959 / 1000000000000000000))) +
      6 * ((1600346771 / 1000000000000000000)) * ((384643959 / 1000000000000000000)) * (126 / 100) + 8 * ((384643959 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12470 161) (d.f1 12470 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12470 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12470 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12470 161) (d.f1 12470 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12470 161) (d.w1 12470 161) (d.w2 12470 161)
  have hwexpr0 : 0 ≤ d.w0 12470 161 + d.w1 12470 161 * √(π / 2) +
      2 * d.w2 12470 161 + energyR16 12470 *
      radiusPolynomialRoot16 (d.w0 12470 161) (d.w1 12470 161) (d.w2 12470 161) := by
    positivity
  constructor
  · change (12470 : ℝ) ^ 8 * (mA 12470 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12470 161) (d.f1 12470 161) d.f2 + locationR16 12470 *
        radiusPolynomialRoot16 (d.f0 12470 161) (d.f1 12470 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12470 : ℝ) ^ 8 * (mA 12470 : ℝ) ^ 8 *
        ((((959391713 / 200000000000000000) : ℝ) ^ 2 + 2 * ((959391713 / 200000000000000000)) * ((1600346771 / 1000000000000000000)) * (126 / 100) +
          2 * (((1600346771 / 1000000000000000000)) ^ 2 + 2 * ((959391713 / 200000000000000000)) * ((384643959 / 1000000000000000000))) +
          6 * ((1600346771 / 1000000000000000000)) * ((384643959 / 1000000000000000000)) * (126 / 100) + 8 * ((384643959 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12470) *
          (32 * (((959391713 / 200000000000000000) : ℝ) + (1600346771 / 1000000000000000000) + (384643959 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12470 : ℝ) ^ 16 *
      (d.w0 12470 161 + d.w1 12470 161 * √(π / 2) + 2 * d.w2 12470 161 +
        energyR16 12470 * radiusPolynomialRoot16 (d.w0 12470 161) (d.w1 12470 161)
          (d.w2 12470 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12470 : ℝ) ^ 16 *
        (((968261611 / 50000000000000000000) : ℝ) + ((275559867 / 20000000000000000000)) * (126 / 100) + 2 * ((251706873 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12470) *
          (32 * (((968261611 / 50000000000000000000) : ℝ) + (275559867 / 20000000000000000000) + (251706873 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12470

/-! A coarse bound on the actual paper statistics constant at dimension 12471. -/
namespace BstLean.Part266.Row12471
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12469 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12469 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12469 128 ≤ (12723 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12723 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12471) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12471 : ℕ))
    (by norm_num : (12471 : ℕ) ≤ 16384)
  have ht : paperTail256 12471 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12471 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12471 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12471 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12471 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12471 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12469 128 * √(2 / (12471 : ℝ)) *
      (√(12471 : ℝ) + paperT0 12471 + paperTail256 12471) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12471 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12471 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12471 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12469 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12469 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12471 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12471

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12471
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12471 (61 / 100) 161 (17 / (100 * 12471)) (26 / (10 * 12471)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12471 (61 / 100) 161 (17 / (100 * 12471)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (50328691 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (807131613 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1184440649 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12471 / 12471 * (61 / 100)) ^ 4 * inverseRadius8 (12471 - 1) /
            envelopeGap 12471 (61 / 100) 161 (17 / (100 * 12471)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12471

namespace BstLean.Part266.Row12471
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12471 161 ≤ (2397998401 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12471 161 ≤ (64001037 / 40000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (6008857 / 15625000000000000)
  w0 : (tableEnvelope C).w0 12471 161 ≤ (24200717 / 1250000000000000000)
  w1 : (tableEnvelope C).w1 12471 161 ≤ (137746789 / 10000000000000000000)
  w2 : (tableEnvelope C).w2 12471 161 ≤ (503292647 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (50328691 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (50328691 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (807131613 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1184440649 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3692103 / 1000000000) : ℝ) ≤ √(17 / (100 * 12471) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12471) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2243405693 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (5022236843 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12471) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12471) ≤ (56700087 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12471) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12471 * (161 : ℝ) ^ 2 + 26 / (10 * 12471) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12471) : ℝ)) (tA 12471 * 161 ^ 2 + 26 / (10 * 12471)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3692103 / 1000000000))) * ((50328691 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3692103 / 1000000000)) ^ 3) * ((807131613 / 500000000000000000000000))) + ((1184440649 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3692103 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12471) : ℝ)) d.D d.V d.P (√(tA 12471) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3692103 / 1000000000)) ^ 2 * (((2243405693 / 1000000000000000)) * ((5022236843 / 125000000000000000)))) + ((1184440649 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12471) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3692103 / 1000000000)) * ((50328691 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12471) : ℝ)) (tA 12471 * 161 ^ 2 + 26 / (10 * 12471)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((50328691 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3692103 / 1000000000)) ^ 2) * ((807131613 / 500000000000000000000000)) + ((1184440649 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12471) : ℝ)) (√(26 / (10 * 12471) : ℝ)) d.D d.V d.P (√(tA 12471) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3692103 / 1000000000)) * (((2243405693 / 1000000000000000)) * ((5022236843 / 125000000000000000))) + ((1184440649 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12471) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((50328691 / 10000000000000000000) : ℝ) + ((1184440649 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12471

namespace BstLean.Part266.Row12471
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12471 161 ∧
    0 ≤ (tableEnvelope C).f1 12471 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12471 161 ∧
    0 ≤ (tableEnvelope C).w1 12471 161 ∧ 0 ≤ (tableEnvelope C).w2 12471 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12471 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12471 161 ∧ 0 ≤ d.f1 12471 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12471 161 ∧ 0 ≤ d.w1 12471 161 ∧ 0 ≤ d.w2 12471 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12471 ≤ 2 * (228 / 100 : ℝ) / 12471 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12471 ≤ 2 * (370 / 100 : ℝ) / 12471 := by
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
    (completeRAData (tableEnvelope C) 12471 161).locationBound 12471 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12471 161).energyBound 12471 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12471 161) (d.f1 12471 161) d.f2 ≤
      32 * (((2397998401 / 500000000000000000) : ℝ) + (64001037 / 40000000000000000) + (6008857 / 15625000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12471 161) (d.w1 12471 161)
      (d.w2 12471 161) ≤
      32 * (((24200717 / 1250000000000000000) : ℝ) + (137746789 / 10000000000000000000) + (503292647 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12471 161) (d.f1 12471 161) d.f2 ≤
      ((2397998401 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2397998401 / 500000000000000000)) * ((64001037 / 40000000000000000)) * (126 / 100) +
      2 * (((64001037 / 40000000000000000)) ^ 2 + 2 * ((2397998401 / 500000000000000000)) * ((6008857 / 15625000000000000))) +
      6 * ((64001037 / 40000000000000000)) * ((6008857 / 15625000000000000)) * (126 / 100) + 8 * ((6008857 / 15625000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12471 161) (d.f1 12471 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12471 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12471 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12471 161) (d.f1 12471 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12471 161) (d.w1 12471 161) (d.w2 12471 161)
  have hwexpr0 : 0 ≤ d.w0 12471 161 + d.w1 12471 161 * √(π / 2) +
      2 * d.w2 12471 161 + energyR16 12471 *
      radiusPolynomialRoot16 (d.w0 12471 161) (d.w1 12471 161) (d.w2 12471 161) := by
    positivity
  constructor
  · change (12471 : ℝ) ^ 8 * (mA 12471 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12471 161) (d.f1 12471 161) d.f2 + locationR16 12471 *
        radiusPolynomialRoot16 (d.f0 12471 161) (d.f1 12471 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12471 : ℝ) ^ 8 * (mA 12471 : ℝ) ^ 8 *
        ((((2397998401 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2397998401 / 500000000000000000)) * ((64001037 / 40000000000000000)) * (126 / 100) +
          2 * (((64001037 / 40000000000000000)) ^ 2 + 2 * ((2397998401 / 500000000000000000)) * ((6008857 / 15625000000000000))) +
          6 * ((64001037 / 40000000000000000)) * ((6008857 / 15625000000000000)) * (126 / 100) + 8 * ((6008857 / 15625000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12471) *
          (32 * (((2397998401 / 500000000000000000) : ℝ) + (64001037 / 40000000000000000) + (6008857 / 15625000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12471 : ℝ) ^ 16 *
      (d.w0 12471 161 + d.w1 12471 161 * √(π / 2) + 2 * d.w2 12471 161 +
        energyR16 12471 * radiusPolynomialRoot16 (d.w0 12471 161) (d.w1 12471 161)
          (d.w2 12471 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12471 : ℝ) ^ 16 *
        (((24200717 / 1250000000000000000) : ℝ) + ((137746789 / 10000000000000000000)) * (126 / 100) + 2 * ((503292647 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12471) *
          (32 * (((24200717 / 1250000000000000000) : ℝ) + (137746789 / 10000000000000000000) + (503292647 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12471

/-! A coarse bound on the actual paper statistics constant at dimension 12472. -/
namespace BstLean.Part266.Row12472
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12470 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12470 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12470 128 ≤ (12724 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12724 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12472) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12472 : ℕ))
    (by norm_num : (12472 : ℕ) ≤ 16384)
  have ht : paperTail256 12472 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12472 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12472 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12472 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12472 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12472 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12470 128 * √(2 / (12472 : ℝ)) *
      (√(12472 : ℝ) + paperT0 12472 + paperTail256 12472) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12472 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12472 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12472 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12470 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12470 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12472 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12472

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12472
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12472 (61 / 100) 161 (17 / (100 * 12472)) (26 / (10 * 12472)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12472 (61 / 100) 161 (17 / (100 * 12472)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (503165853 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1613745543 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5918368171 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12472 / 12472 * (61 / 100)) ^ 4 * inverseRadius8 (12472 - 1) /
            envelopeGap 12472 (61 / 100) 161 (17 / (100 * 12472)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12472

namespace BstLean.Part266.Row12472
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12472 161 ≤ (2397517687 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12472 161 ≤ (1599705183 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (384489759 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12472 161 ≤ (96779583 / 5000000000000000000)
  w1 : (tableEnvelope C).w1 12472 161 ≤ (344284139 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12472 161 ≤ (503171587 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (503165853 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (503165853 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1613745543 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5918368171 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((738391 / 200000000) : ℝ) ≤ √(17 / (100 * 12472) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12472) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (224313587 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40171451841 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12472) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12472) ≤ (56695541 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12472) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12472 * (161 : ℝ) ^ 2 + 26 / (10 * 12472) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12472) : ℝ)) (tA 12472 * 161 ^ 2 + 26 / (10 * 12472)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((738391 / 200000000))) * ((503165853 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((738391 / 200000000)) ^ 3) * ((1613745543 / 1000000000000000000000000))) + ((5918368171 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((738391 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12472) : ℝ)) d.D d.V d.P (√(tA 12472) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((738391 / 200000000)) ^ 2 * (((224313587 / 100000000000000)) * ((40171451841 / 1000000000000000000)))) + ((5918368171 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12472) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((738391 / 200000000)) * ((503165853 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12472) : ℝ)) (tA 12472 * 161 ^ 2 + 26 / (10 * 12472)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((503165853 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((738391 / 200000000)) ^ 2) * ((1613745543 / 1000000000000000000000000)) + ((5918368171 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12472) : ℝ)) (√(26 / (10 * 12472) : ℝ)) d.D d.V d.P (√(tA 12472) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((738391 / 200000000)) * (((224313587 / 100000000000000)) * ((40171451841 / 1000000000000000000))) + ((5918368171 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12472) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((503165853 / 100000000000000000000) : ℝ) + ((5918368171 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12472

namespace BstLean.Part266.Row12472
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12472 161 ∧
    0 ≤ (tableEnvelope C).f1 12472 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12472 161 ∧
    0 ≤ (tableEnvelope C).w1 12472 161 ∧ 0 ≤ (tableEnvelope C).w2 12472 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12472 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12472 161 ∧ 0 ≤ d.f1 12472 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12472 161 ∧ 0 ≤ d.w1 12472 161 ∧ 0 ≤ d.w2 12472 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12472 ≤ 2 * (228 / 100 : ℝ) / 12472 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12472 ≤ 2 * (370 / 100 : ℝ) / 12472 := by
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
    (completeRAData (tableEnvelope C) 12472 161).locationBound 12472 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12472 161).energyBound 12472 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12472 161) (d.f1 12472 161) d.f2 ≤
      32 * (((2397517687 / 500000000000000000) : ℝ) + (1599705183 / 1000000000000000000) + (384489759 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12472 161) (d.w1 12472 161)
      (d.w2 12472 161) ≤
      32 * (((96779583 / 5000000000000000000) : ℝ) + (344284139 / 25000000000000000000) + (503171587 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12472 161) (d.f1 12472 161) d.f2 ≤
      ((2397517687 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2397517687 / 500000000000000000)) * ((1599705183 / 1000000000000000000)) * (126 / 100) +
      2 * (((1599705183 / 1000000000000000000)) ^ 2 + 2 * ((2397517687 / 500000000000000000)) * ((384489759 / 1000000000000000000))) +
      6 * ((1599705183 / 1000000000000000000)) * ((384489759 / 1000000000000000000)) * (126 / 100) + 8 * ((384489759 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12472 161) (d.f1 12472 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12472 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12472 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12472 161) (d.f1 12472 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12472 161) (d.w1 12472 161) (d.w2 12472 161)
  have hwexpr0 : 0 ≤ d.w0 12472 161 + d.w1 12472 161 * √(π / 2) +
      2 * d.w2 12472 161 + energyR16 12472 *
      radiusPolynomialRoot16 (d.w0 12472 161) (d.w1 12472 161) (d.w2 12472 161) := by
    positivity
  constructor
  · change (12472 : ℝ) ^ 8 * (mA 12472 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12472 161) (d.f1 12472 161) d.f2 + locationR16 12472 *
        radiusPolynomialRoot16 (d.f0 12472 161) (d.f1 12472 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12472 : ℝ) ^ 8 * (mA 12472 : ℝ) ^ 8 *
        ((((2397517687 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2397517687 / 500000000000000000)) * ((1599705183 / 1000000000000000000)) * (126 / 100) +
          2 * (((1599705183 / 1000000000000000000)) ^ 2 + 2 * ((2397517687 / 500000000000000000)) * ((384489759 / 1000000000000000000))) +
          6 * ((1599705183 / 1000000000000000000)) * ((384489759 / 1000000000000000000)) * (126 / 100) + 8 * ((384489759 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12472) *
          (32 * (((2397517687 / 500000000000000000) : ℝ) + (1599705183 / 1000000000000000000) + (384489759 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12472 : ℝ) ^ 16 *
      (d.w0 12472 161 + d.w1 12472 161 * √(π / 2) + 2 * d.w2 12472 161 +
        energyR16 12472 * radiusPolynomialRoot16 (d.w0 12472 161) (d.w1 12472 161)
          (d.w2 12472 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12472 : ℝ) ^ 16 *
        (((96779583 / 5000000000000000000) : ℝ) + ((344284139 / 25000000000000000000)) * (126 / 100) + 2 * ((503171587 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12472) *
          (32 * (((96779583 / 5000000000000000000) : ℝ) + (344284139 / 25000000000000000000) + (503171587 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12472

/-! A coarse bound on the actual paper statistics constant at dimension 12473. -/
namespace BstLean.Part266.Row12473
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12471 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12471 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12471 128 ≤ (12725 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12725 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12473) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12473 : ℕ))
    (by norm_num : (12473 : ℕ) ≤ 16384)
  have ht : paperTail256 12473 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12473 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12473 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12473 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12473 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12473 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12471 128 * √(2 / (12473 : ℝ)) *
      (√(12473 : ℝ) + paperT0 12473 + paperTail256 12473) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12473 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12473 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12473 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12471 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12471 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12473 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12473

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12473
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12473 (61 / 100) 161 (17 / (100 * 12473)) (26 / (10 * 12473)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12473 (61 / 100) 161 (17 / (100 * 12473)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (100608967 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1613228069 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2957267947 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12473 / 12473 * (61 / 100)) ^ 4 * inverseRadius8 (12473 - 1) /
            envelopeGap 12473 (61 / 100) 161 (17 / (100 * 12473)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12473

namespace BstLean.Part266.Row12473
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12473 161 ≤ (2397037143 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12473 161 ≤ (1599384547 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (76882539 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12473 161 ≤ (483781531 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12473 161 ≤ (1376805337 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12473 161 ≤ (100610113 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (100608967 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (100608967 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1613228069 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2957267947 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3691807 / 1000000000) : ℝ) ≤ √(17 / (100 * 12473) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12473) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1121433051 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40165010507 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12473) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12473) ≤ (113381991 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12473) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12473 * (161 : ℝ) ^ 2 + 26 / (10 * 12473) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12473) : ℝ)) (tA 12473 * 161 ^ 2 + 26 / (10 * 12473)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3691807 / 1000000000))) * ((100608967 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3691807 / 1000000000)) ^ 3) * ((1613228069 / 1000000000000000000000000))) + ((2957267947 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3691807 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12473) : ℝ)) d.D d.V d.P (√(tA 12473) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3691807 / 1000000000)) ^ 2 * (((1121433051 / 500000000000000)) * ((40165010507 / 1000000000000000000)))) + ((2957267947 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12473) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3691807 / 1000000000)) * ((100608967 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12473) : ℝ)) (tA 12473 * 161 ^ 2 + 26 / (10 * 12473)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((100608967 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3691807 / 1000000000)) ^ 2) * ((1613228069 / 1000000000000000000000000)) + ((2957267947 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12473) : ℝ)) (√(26 / (10 * 12473) : ℝ)) d.D d.V d.P (√(tA 12473) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3691807 / 1000000000)) * (((1121433051 / 500000000000000)) * ((40165010507 / 1000000000000000000))) + ((2957267947 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12473) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((100608967 / 20000000000000000000) : ℝ) + ((2957267947 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12473

namespace BstLean.Part266.Row12473
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12473 161 ∧
    0 ≤ (tableEnvelope C).f1 12473 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12473 161 ∧
    0 ≤ (tableEnvelope C).w1 12473 161 ∧ 0 ≤ (tableEnvelope C).w2 12473 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12473 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12473 161 ∧ 0 ≤ d.f1 12473 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12473 161 ∧ 0 ≤ d.w1 12473 161 ∧ 0 ≤ d.w2 12473 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12473 ≤ 2 * (228 / 100 : ℝ) / 12473 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12473 ≤ 2 * (370 / 100 : ℝ) / 12473 := by
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
    (completeRAData (tableEnvelope C) 12473 161).locationBound 12473 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12473 161).energyBound 12473 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12473 161) (d.f1 12473 161) d.f2 ≤
      32 * (((2397037143 / 500000000000000000) : ℝ) + (1599384547 / 1000000000000000000) + (76882539 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12473 161) (d.w1 12473 161)
      (d.w2 12473 161) ≤
      32 * (((483781531 / 25000000000000000000) : ℝ) + (1376805337 / 100000000000000000000) + (100610113 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12473 161) (d.f1 12473 161) d.f2 ≤
      ((2397037143 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2397037143 / 500000000000000000)) * ((1599384547 / 1000000000000000000)) * (126 / 100) +
      2 * (((1599384547 / 1000000000000000000)) ^ 2 + 2 * ((2397037143 / 500000000000000000)) * ((76882539 / 200000000000000000))) +
      6 * ((1599384547 / 1000000000000000000)) * ((76882539 / 200000000000000000)) * (126 / 100) + 8 * ((76882539 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12473 161) (d.f1 12473 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12473 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12473 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12473 161) (d.f1 12473 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12473 161) (d.w1 12473 161) (d.w2 12473 161)
  have hwexpr0 : 0 ≤ d.w0 12473 161 + d.w1 12473 161 * √(π / 2) +
      2 * d.w2 12473 161 + energyR16 12473 *
      radiusPolynomialRoot16 (d.w0 12473 161) (d.w1 12473 161) (d.w2 12473 161) := by
    positivity
  constructor
  · change (12473 : ℝ) ^ 8 * (mA 12473 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12473 161) (d.f1 12473 161) d.f2 + locationR16 12473 *
        radiusPolynomialRoot16 (d.f0 12473 161) (d.f1 12473 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12473 : ℝ) ^ 8 * (mA 12473 : ℝ) ^ 8 *
        ((((2397037143 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2397037143 / 500000000000000000)) * ((1599384547 / 1000000000000000000)) * (126 / 100) +
          2 * (((1599384547 / 1000000000000000000)) ^ 2 + 2 * ((2397037143 / 500000000000000000)) * ((76882539 / 200000000000000000))) +
          6 * ((1599384547 / 1000000000000000000)) * ((76882539 / 200000000000000000)) * (126 / 100) + 8 * ((76882539 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12473) *
          (32 * (((2397037143 / 500000000000000000) : ℝ) + (1599384547 / 1000000000000000000) + (76882539 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12473 : ℝ) ^ 16 *
      (d.w0 12473 161 + d.w1 12473 161 * √(π / 2) + 2 * d.w2 12473 161 +
        energyR16 12473 * radiusPolynomialRoot16 (d.w0 12473 161) (d.w1 12473 161)
          (d.w2 12473 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12473 : ℝ) ^ 16 *
        (((483781531 / 25000000000000000000) : ℝ) + ((1376805337 / 100000000000000000000)) * (126 / 100) + 2 * ((100610113 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12473) *
          (32 * (((483781531 / 25000000000000000000) : ℝ) + (1376805337 / 100000000000000000000) + (100610113 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12473

/-! A coarse bound on the actual paper statistics constant at dimension 12474. -/
namespace BstLean.Part266.Row12474
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12472 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12472 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12472 128 ≤ (12726 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12726 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12474) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12474 : ℕ))
    (by norm_num : (12474 : ℕ) ≤ 16384)
  have ht : paperTail256 12474 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12474 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12474 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12474 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12474 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12474 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12472 128 * √(2 / (12474 : ℝ)) *
      (√(12474 : ℝ) + paperT0 12474 + paperTail256 12474) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12474 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12474 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12474 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12472 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12472 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12474 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12474

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12474
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12474 (61 / 100) 161 (17 / (100 * 12474)) (26 / (10 * 12474)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12474 (61 / 100) 161 (17 / (100 * 12474)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (31432741 / 6250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1612710801 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (591070641 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12474 / 12474 * (61 / 100)) ^ 4 * inverseRadius8 (12474 - 1) /
            envelopeGap 12474 (61 / 100) 161 (17 / (100 * 12474)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12474

namespace BstLean.Part266.Row12474
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12474 161 ≤ (4793113531 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12474 161 ≤ (1599064017 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (384335653 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12474 161 ≤ (1934660751 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12474 161 ≤ (137647423 / 10000000000000000000)
  w2 : (tableEnvelope C).w2 12474 161 ≤ (251464791 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (31432741 / 6250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (31432741 / 6250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1612710801 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (591070641 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3691659 / 1000000000) : ℝ) ≤ √(17 / (100 * 12474) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12474) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2242596389 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (8031714141 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12474) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12474) ≤ (113372901 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12474) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12474 * (161 : ℝ) ^ 2 + 26 / (10 * 12474) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12474) : ℝ)) (tA 12474 * 161 ^ 2 + 26 / (10 * 12474)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3691659 / 1000000000))) * ((31432741 / 6250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3691659 / 1000000000)) ^ 3) * ((1612710801 / 1000000000000000000000000))) + ((591070641 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3691659 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12474) : ℝ)) d.D d.V d.P (√(tA 12474) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3691659 / 1000000000)) ^ 2 * (((2242596389 / 1000000000000000)) * ((8031714141 / 200000000000000000)))) + ((591070641 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12474) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3691659 / 1000000000)) * ((31432741 / 6250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12474) : ℝ)) (tA 12474 * 161 ^ 2 + 26 / (10 * 12474)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((31432741 / 6250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3691659 / 1000000000)) ^ 2) * ((1612710801 / 1000000000000000000000000)) + ((591070641 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12474) : ℝ)) (√(26 / (10 * 12474) : ℝ)) d.D d.V d.P (√(tA 12474) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3691659 / 1000000000)) * (((2242596389 / 1000000000000000)) * ((8031714141 / 200000000000000000))) + ((591070641 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12474) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((31432741 / 6250000000000000000) : ℝ) + ((591070641 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12474

namespace BstLean.Part266.Row12474
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12474 161 ∧
    0 ≤ (tableEnvelope C).f1 12474 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12474 161 ∧
    0 ≤ (tableEnvelope C).w1 12474 161 ∧ 0 ≤ (tableEnvelope C).w2 12474 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12474 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12474 161 ∧ 0 ≤ d.f1 12474 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12474 161 ∧ 0 ≤ d.w1 12474 161 ∧ 0 ≤ d.w2 12474 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12474 ≤ 2 * (228 / 100 : ℝ) / 12474 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12474 ≤ 2 * (370 / 100 : ℝ) / 12474 := by
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
    (completeRAData (tableEnvelope C) 12474 161).locationBound 12474 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12474 161).energyBound 12474 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12474 161) (d.f1 12474 161) d.f2 ≤
      32 * (((4793113531 / 1000000000000000000) : ℝ) + (1599064017 / 1000000000000000000) + (384335653 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12474 161) (d.w1 12474 161)
      (d.w2 12474 161) ≤
      32 * (((1934660751 / 100000000000000000000) : ℝ) + (137647423 / 10000000000000000000) + (251464791 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12474 161) (d.f1 12474 161) d.f2 ≤
      ((4793113531 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4793113531 / 1000000000000000000)) * ((1599064017 / 1000000000000000000)) * (126 / 100) +
      2 * (((1599064017 / 1000000000000000000)) ^ 2 + 2 * ((4793113531 / 1000000000000000000)) * ((384335653 / 1000000000000000000))) +
      6 * ((1599064017 / 1000000000000000000)) * ((384335653 / 1000000000000000000)) * (126 / 100) + 8 * ((384335653 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12474 161) (d.f1 12474 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12474 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12474 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12474 161) (d.f1 12474 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12474 161) (d.w1 12474 161) (d.w2 12474 161)
  have hwexpr0 : 0 ≤ d.w0 12474 161 + d.w1 12474 161 * √(π / 2) +
      2 * d.w2 12474 161 + energyR16 12474 *
      radiusPolynomialRoot16 (d.w0 12474 161) (d.w1 12474 161) (d.w2 12474 161) := by
    positivity
  constructor
  · change (12474 : ℝ) ^ 8 * (mA 12474 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12474 161) (d.f1 12474 161) d.f2 + locationR16 12474 *
        radiusPolynomialRoot16 (d.f0 12474 161) (d.f1 12474 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12474 : ℝ) ^ 8 * (mA 12474 : ℝ) ^ 8 *
        ((((4793113531 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4793113531 / 1000000000000000000)) * ((1599064017 / 1000000000000000000)) * (126 / 100) +
          2 * (((1599064017 / 1000000000000000000)) ^ 2 + 2 * ((4793113531 / 1000000000000000000)) * ((384335653 / 1000000000000000000))) +
          6 * ((1599064017 / 1000000000000000000)) * ((384335653 / 1000000000000000000)) * (126 / 100) + 8 * ((384335653 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12474) *
          (32 * (((4793113531 / 1000000000000000000) : ℝ) + (1599064017 / 1000000000000000000) + (384335653 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12474 : ℝ) ^ 16 *
      (d.w0 12474 161 + d.w1 12474 161 * √(π / 2) + 2 * d.w2 12474 161 +
        energyR16 12474 * radiusPolynomialRoot16 (d.w0 12474 161) (d.w1 12474 161)
          (d.w2 12474 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12474 : ℝ) ^ 16 *
        (((1934660751 / 100000000000000000000) : ℝ) + ((137647423 / 10000000000000000000)) * (126 / 100) + 2 * ((251464791 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12474) *
          (32 * (((1934660751 / 100000000000000000000) : ℝ) + (137647423 / 10000000000000000000) + (251464791 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12474
