import BstLean.Part266Shard1Step4


/-! A coarse bound on the actual paper statistics constant at dimension 12375. -/
namespace BstLean.Part266.Row12375
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12373 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12373 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12373 128 ≤ (12627 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12627 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12375) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12375 : ℕ))
    (by norm_num : (12375 : ℕ) ≤ 16384)
  have ht : paperTail256 12375 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12375 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12375 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12375 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12375 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12375 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12373 128 * √(2 / (12375 : ℝ)) *
      (√(12375 : ℝ) + paperT0 12375 + paperTail256 12375) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12375 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12375 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12375 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12373 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12373 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12375 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12375

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12375
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12375 (61 / 100) 161 (17 / (100 * 12375)) (26 / (10 * 12375)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12375 (61 / 100) 161 (17 / (100 * 12375)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (128772877 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1664942273 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3151872127 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12375 / 12375 * (61 / 100)) ^ 4 * inverseRadius8 (12375 - 1) /
            envelopeGap 12375 (61 / 100) 161 (17 / (100 * 12375)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12375

namespace BstLean.Part266.Row12375
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12375 161 ≤ (1222389719 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12375 161 ≤ (407809939 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (196034537 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12375 161 ≤ (990733913 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12375 161 ≤ (1409776529 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12375 161 ≤ (103019523 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (128772877 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (128772877 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1664942273 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3151872127 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((926599 / 250000000) : ℝ) ≤ √(17 / (100 * 12375) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12375) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2269562751 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (20401852079 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12375) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12375) ≤ (28569971 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12375) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12375 * (161 : ℝ) ^ 2 + 26 / (10 * 12375) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12375) : ℝ)) (tA 12375 * 161 ^ 2 + 26 / (10 * 12375)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((926599 / 250000000))) * ((128772877 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((926599 / 250000000)) ^ 3) * ((1664942273 / 1000000000000000000000000))) + ((3151872127 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((926599 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12375) : ℝ)) d.D d.V d.P (√(tA 12375) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((926599 / 250000000)) ^ 2 * (((2269562751 / 1000000000000000)) * ((20401852079 / 500000000000000000)))) + ((3151872127 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12375) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((926599 / 250000000)) * ((128772877 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12375) : ℝ)) (tA 12375 * 161 ^ 2 + 26 / (10 * 12375)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((128772877 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((926599 / 250000000)) ^ 2) * ((1664942273 / 1000000000000000000000000)) + ((3151872127 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12375) : ℝ)) (√(26 / (10 * 12375) : ℝ)) d.D d.V d.P (√(tA 12375) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((926599 / 250000000)) * (((2269562751 / 1000000000000000)) * ((20401852079 / 500000000000000000))) + ((3151872127 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12375) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((128772877 / 25000000000000000000) : ℝ) + ((3151872127 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12375

namespace BstLean.Part266.Row12375
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12375 161 ∧
    0 ≤ (tableEnvelope C).f1 12375 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12375 161 ∧
    0 ≤ (tableEnvelope C).w1 12375 161 ∧ 0 ≤ (tableEnvelope C).w2 12375 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12375 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12375 161 ∧ 0 ≤ d.f1 12375 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12375 161 ∧ 0 ≤ d.w1 12375 161 ∧ 0 ≤ d.w2 12375 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12375 ≤ 2 * (228 / 100 : ℝ) / 12375 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12375 ≤ 2 * (370 / 100 : ℝ) / 12375 := by
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
    (completeRAData (tableEnvelope C) 12375 161).locationBound 12375 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12375 161).energyBound 12375 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12375 161) (d.f1 12375 161) d.f2 ≤
      32 * (((1222389719 / 250000000000000000) : ℝ) + (407809939 / 250000000000000000) + (196034537 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12375 161) (d.w1 12375 161)
      (d.w2 12375 161) ≤
      32 * (((990733913 / 50000000000000000000) : ℝ) + (1409776529 / 100000000000000000000) + (103019523 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12375 161) (d.f1 12375 161) d.f2 ≤
      ((1222389719 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1222389719 / 250000000000000000)) * ((407809939 / 250000000000000000)) * (126 / 100) +
      2 * (((407809939 / 250000000000000000)) ^ 2 + 2 * ((1222389719 / 250000000000000000)) * ((196034537 / 500000000000000000))) +
      6 * ((407809939 / 250000000000000000)) * ((196034537 / 500000000000000000)) * (126 / 100) + 8 * ((196034537 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12375 161) (d.f1 12375 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12375 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12375 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12375 161) (d.f1 12375 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12375 161) (d.w1 12375 161) (d.w2 12375 161)
  have hwexpr0 : 0 ≤ d.w0 12375 161 + d.w1 12375 161 * √(π / 2) +
      2 * d.w2 12375 161 + energyR16 12375 *
      radiusPolynomialRoot16 (d.w0 12375 161) (d.w1 12375 161) (d.w2 12375 161) := by
    positivity
  constructor
  · change (12375 : ℝ) ^ 8 * (mA 12375 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12375 161) (d.f1 12375 161) d.f2 + locationR16 12375 *
        radiusPolynomialRoot16 (d.f0 12375 161) (d.f1 12375 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12375 : ℝ) ^ 8 * (mA 12375 : ℝ) ^ 8 *
        ((((1222389719 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1222389719 / 250000000000000000)) * ((407809939 / 250000000000000000)) * (126 / 100) +
          2 * (((407809939 / 250000000000000000)) ^ 2 + 2 * ((1222389719 / 250000000000000000)) * ((196034537 / 500000000000000000))) +
          6 * ((407809939 / 250000000000000000)) * ((196034537 / 500000000000000000)) * (126 / 100) + 8 * ((196034537 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12375) *
          (32 * (((1222389719 / 250000000000000000) : ℝ) + (407809939 / 250000000000000000) + (196034537 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12375 : ℝ) ^ 16 *
      (d.w0 12375 161 + d.w1 12375 161 * √(π / 2) + 2 * d.w2 12375 161 +
        energyR16 12375 * radiusPolynomialRoot16 (d.w0 12375 161) (d.w1 12375 161)
          (d.w2 12375 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12375 : ℝ) ^ 16 *
        (((990733913 / 50000000000000000000) : ℝ) + ((1409776529 / 100000000000000000000)) * (126 / 100) + 2 * ((103019523 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12375) *
          (32 * (((990733913 / 50000000000000000000) : ℝ) + (1409776529 / 100000000000000000000) + (103019523 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12375

/-! A coarse bound on the actual paper statistics constant at dimension 12376. -/
namespace BstLean.Part266.Row12376
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12374 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12374 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12374 128 ≤ (12628 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12628 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12376) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12376 : ℕ))
    (by norm_num : (12376 : ℕ) ≤ 16384)
  have ht : paperTail256 12376 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12376 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12376 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12376 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12376 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12376 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12374 128 * √(2 / (12376 : ℝ)) *
      (√(12376 : ℝ) + paperT0 12376 + paperTail256 12376) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12376 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12376 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12376 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12374 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12374 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12376 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12376

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12376
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12376 (61 / 100) 161 (17 / (100 * 12376)) (26 / (10 * 12376)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12376 (61 / 100) 161 (17 / (100 * 12376)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (514966651 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1664404197 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6299629827 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12376 / 12376 * (61 / 100)) ^ 4 * inverseRadius8 (12376 - 1) /
            envelopeGap 12376 (61 / 100) 161 (17 / (100 * 12376)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12376

namespace BstLean.Part266.Row12376
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12376 161 ≤ (611071517 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12376 161 ≤ (1630910463 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (195994951 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12376 161 ≤ (79239509 / 4000000000000000000)
  w1 : (tableEnvelope C).w1 12376 161 ≤ (1409434899 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12376 161 ≤ (257486377 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (514966651 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (514966651 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1664404197 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6299629827 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1853123 / 500000000) : ℝ) ≤ √(17 / (100 * 12376) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12376) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1134643833 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (10199277539 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12376) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12376) ≤ (2285413 / 20000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12376) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12376 * (161 : ℝ) ^ 2 + 26 / (10 * 12376) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12376) : ℝ)) (tA 12376 * 161 ^ 2 + 26 / (10 * 12376)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1853123 / 500000000))) * ((514966651 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1853123 / 500000000)) ^ 3) * ((1664404197 / 1000000000000000000000000))) + ((6299629827 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1853123 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12376) : ℝ)) d.D d.V d.P (√(tA 12376) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1853123 / 500000000)) ^ 2 * (((1134643833 / 500000000000000)) * ((10199277539 / 250000000000000000)))) + ((6299629827 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12376) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1853123 / 500000000)) * ((514966651 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12376) : ℝ)) (tA 12376 * 161 ^ 2 + 26 / (10 * 12376)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((514966651 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1853123 / 500000000)) ^ 2) * ((1664404197 / 1000000000000000000000000)) + ((6299629827 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12376) : ℝ)) (√(26 / (10 * 12376) : ℝ)) d.D d.V d.P (√(tA 12376) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1853123 / 500000000)) * (((1134643833 / 500000000000000)) * ((10199277539 / 250000000000000000))) + ((6299629827 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12376) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((514966651 / 100000000000000000000) : ℝ) + ((6299629827 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12376

namespace BstLean.Part266.Row12376
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12376 161 ∧
    0 ≤ (tableEnvelope C).f1 12376 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12376 161 ∧
    0 ≤ (tableEnvelope C).w1 12376 161 ∧ 0 ≤ (tableEnvelope C).w2 12376 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12376 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12376 161 ∧ 0 ≤ d.f1 12376 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12376 161 ∧ 0 ≤ d.w1 12376 161 ∧ 0 ≤ d.w2 12376 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12376 ≤ 2 * (228 / 100 : ℝ) / 12376 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12376 ≤ 2 * (370 / 100 : ℝ) / 12376 := by
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
    (completeRAData (tableEnvelope C) 12376 161).locationBound 12376 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12376 161).energyBound 12376 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12376 161) (d.f1 12376 161) d.f2 ≤
      32 * (((611071517 / 125000000000000000) : ℝ) + (1630910463 / 1000000000000000000) + (195994951 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12376 161) (d.w1 12376 161)
      (d.w2 12376 161) ≤
      32 * (((79239509 / 4000000000000000000) : ℝ) + (1409434899 / 100000000000000000000) + (257486377 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12376 161) (d.f1 12376 161) d.f2 ≤
      ((611071517 / 125000000000000000) : ℝ) ^ 2 + 2 * ((611071517 / 125000000000000000)) * ((1630910463 / 1000000000000000000)) * (126 / 100) +
      2 * (((1630910463 / 1000000000000000000)) ^ 2 + 2 * ((611071517 / 125000000000000000)) * ((195994951 / 500000000000000000))) +
      6 * ((1630910463 / 1000000000000000000)) * ((195994951 / 500000000000000000)) * (126 / 100) + 8 * ((195994951 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12376 161) (d.f1 12376 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12376 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12376 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12376 161) (d.f1 12376 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12376 161) (d.w1 12376 161) (d.w2 12376 161)
  have hwexpr0 : 0 ≤ d.w0 12376 161 + d.w1 12376 161 * √(π / 2) +
      2 * d.w2 12376 161 + energyR16 12376 *
      radiusPolynomialRoot16 (d.w0 12376 161) (d.w1 12376 161) (d.w2 12376 161) := by
    positivity
  constructor
  · change (12376 : ℝ) ^ 8 * (mA 12376 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12376 161) (d.f1 12376 161) d.f2 + locationR16 12376 *
        radiusPolynomialRoot16 (d.f0 12376 161) (d.f1 12376 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12376 : ℝ) ^ 8 * (mA 12376 : ℝ) ^ 8 *
        ((((611071517 / 125000000000000000) : ℝ) ^ 2 + 2 * ((611071517 / 125000000000000000)) * ((1630910463 / 1000000000000000000)) * (126 / 100) +
          2 * (((1630910463 / 1000000000000000000)) ^ 2 + 2 * ((611071517 / 125000000000000000)) * ((195994951 / 500000000000000000))) +
          6 * ((1630910463 / 1000000000000000000)) * ((195994951 / 500000000000000000)) * (126 / 100) + 8 * ((195994951 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12376) *
          (32 * (((611071517 / 125000000000000000) : ℝ) + (1630910463 / 1000000000000000000) + (195994951 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12376 : ℝ) ^ 16 *
      (d.w0 12376 161 + d.w1 12376 161 * √(π / 2) + 2 * d.w2 12376 161 +
        energyR16 12376 * radiusPolynomialRoot16 (d.w0 12376 161) (d.w1 12376 161)
          (d.w2 12376 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12376 : ℝ) ^ 16 *
        (((79239509 / 4000000000000000000) : ℝ) + ((1409434899 / 100000000000000000000)) * (126 / 100) + 2 * ((257486377 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12376) *
          (32 * (((79239509 / 4000000000000000000) : ℝ) + (1409434899 / 100000000000000000000) + (257486377 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12376

/-! A coarse bound on the actual paper statistics constant at dimension 12377. -/
namespace BstLean.Part266.Row12377
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12375 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12375 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12375 128 ≤ (12629 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12629 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12377) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12377 : ℕ))
    (by norm_num : (12377 : ℕ) ≤ 16384)
  have ht : paperTail256 12377 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12377 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12377 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12377 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12377 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12377 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12375 128 * √(2 / (12377 : ℝ)) *
      (√(12377 : ℝ) + paperT0 12377 + paperTail256 12377) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12377 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12377 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12377 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12375 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12375 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12377 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12377

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12377
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12377 (61 / 100) 161 (17 / (100 * 12377)) (26 / (10 * 12377)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12377 (61 / 100) 161 (17 / (100 * 12377)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (257420917 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (831933169 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (786939803 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12377 / 12377 * (61 / 100)) ^ 4 * inverseRadius8 (12377 - 1) /
            envelopeGap 12377 (61 / 100) 161 (17 / (100 * 12377)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12377

namespace BstLean.Part266.Row12377
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12377 161 ≤ (4887585743 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12377 161 ≤ (815290639 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (391910753 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12377 161 ≤ (1980507791 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12377 161 ≤ (704546693 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12377 161 ≤ (514847933 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (257420917 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (257420917 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (831933169 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (786939803 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((231631 / 62500000) : ℝ) ≤ √(17 / (100 * 12377) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12377) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (567253159 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40790517747 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12377) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12377) ≤ (57130709 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12377) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12377 * (161 : ℝ) ^ 2 + 26 / (10 * 12377) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12377) : ℝ)) (tA 12377 * 161 ^ 2 + 26 / (10 * 12377)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((231631 / 62500000))) * ((257420917 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((231631 / 62500000)) ^ 3) * ((831933169 / 500000000000000000000000))) + ((786939803 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((231631 / 62500000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12377) : ℝ)) d.D d.V d.P (√(tA 12377) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((231631 / 62500000)) ^ 2 * (((567253159 / 250000000000000)) * ((40790517747 / 1000000000000000000)))) + ((786939803 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12377) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((231631 / 62500000)) * ((257420917 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12377) : ℝ)) (tA 12377 * 161 ^ 2 + 26 / (10 * 12377)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((257420917 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((231631 / 62500000)) ^ 2) * ((831933169 / 500000000000000000000000)) + ((786939803 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12377) : ℝ)) (√(26 / (10 * 12377) : ℝ)) d.D d.V d.P (√(tA 12377) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((231631 / 62500000)) * (((567253159 / 250000000000000)) * ((40790517747 / 1000000000000000000))) + ((786939803 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12377) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((257420917 / 50000000000000000000) : ℝ) + ((786939803 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12377

namespace BstLean.Part266.Row12377
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12377 161 ∧
    0 ≤ (tableEnvelope C).f1 12377 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12377 161 ∧
    0 ≤ (tableEnvelope C).w1 12377 161 ∧ 0 ≤ (tableEnvelope C).w2 12377 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12377 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12377 161 ∧ 0 ≤ d.f1 12377 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12377 161 ∧ 0 ≤ d.w1 12377 161 ∧ 0 ≤ d.w2 12377 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12377 ≤ 2 * (228 / 100 : ℝ) / 12377 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12377 ≤ 2 * (370 / 100 : ℝ) / 12377 := by
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
    (completeRAData (tableEnvelope C) 12377 161).locationBound 12377 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12377 161).energyBound 12377 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12377 161) (d.f1 12377 161) d.f2 ≤
      32 * (((4887585743 / 1000000000000000000) : ℝ) + (815290639 / 500000000000000000) + (391910753 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12377 161) (d.w1 12377 161)
      (d.w2 12377 161) ≤
      32 * (((1980507791 / 100000000000000000000) : ℝ) + (704546693 / 50000000000000000000) + (514847933 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12377 161) (d.f1 12377 161) d.f2 ≤
      ((4887585743 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4887585743 / 1000000000000000000)) * ((815290639 / 500000000000000000)) * (126 / 100) +
      2 * (((815290639 / 500000000000000000)) ^ 2 + 2 * ((4887585743 / 1000000000000000000)) * ((391910753 / 1000000000000000000))) +
      6 * ((815290639 / 500000000000000000)) * ((391910753 / 1000000000000000000)) * (126 / 100) + 8 * ((391910753 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12377 161) (d.f1 12377 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12377 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12377 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12377 161) (d.f1 12377 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12377 161) (d.w1 12377 161) (d.w2 12377 161)
  have hwexpr0 : 0 ≤ d.w0 12377 161 + d.w1 12377 161 * √(π / 2) +
      2 * d.w2 12377 161 + energyR16 12377 *
      radiusPolynomialRoot16 (d.w0 12377 161) (d.w1 12377 161) (d.w2 12377 161) := by
    positivity
  constructor
  · change (12377 : ℝ) ^ 8 * (mA 12377 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12377 161) (d.f1 12377 161) d.f2 + locationR16 12377 *
        radiusPolynomialRoot16 (d.f0 12377 161) (d.f1 12377 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12377 : ℝ) ^ 8 * (mA 12377 : ℝ) ^ 8 *
        ((((4887585743 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4887585743 / 1000000000000000000)) * ((815290639 / 500000000000000000)) * (126 / 100) +
          2 * (((815290639 / 500000000000000000)) ^ 2 + 2 * ((4887585743 / 1000000000000000000)) * ((391910753 / 1000000000000000000))) +
          6 * ((815290639 / 500000000000000000)) * ((391910753 / 1000000000000000000)) * (126 / 100) + 8 * ((391910753 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12377) *
          (32 * (((4887585743 / 1000000000000000000) : ℝ) + (815290639 / 500000000000000000) + (391910753 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12377 : ℝ) ^ 16 *
      (d.w0 12377 161 + d.w1 12377 161 * √(π / 2) + 2 * d.w2 12377 161 +
        energyR16 12377 * radiusPolynomialRoot16 (d.w0 12377 161) (d.w1 12377 161)
          (d.w2 12377 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12377 : ℝ) ^ 16 *
        (((1980507791 / 100000000000000000000) : ℝ) + ((704546693 / 50000000000000000000)) * (126 / 100) + 2 * ((514847933 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12377) *
          (32 * (((1980507791 / 100000000000000000000) : ℝ) + (704546693 / 50000000000000000000) + (514847933 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12377

/-! A coarse bound on the actual paper statistics constant at dimension 12378. -/
namespace BstLean.Part266.Row12378
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12376 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12376 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12376 128 ≤ (12630 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12630 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12378) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12378 : ℕ))
    (by norm_num : (12378 : ℕ) ≤ 16384)
  have ht : paperTail256 12378 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12378 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12378 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12378 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12378 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12378 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12376 128 * √(2 / (12378 : ℝ)) *
      (√(12378 : ℝ) + paperT0 12378 + paperTail256 12378) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12378 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12378 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12378 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12376 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12376 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12378 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12378

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12378
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12378 (61 / 100) 161 (17 / (100 * 12378)) (26 / (10 * 12378)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12378 (61 / 100) 161 (17 / (100 * 12378)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (514717057 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1663328697 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3145705021 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12378 / 12378 * (61 / 100)) ^ 4 * inverseRadius8 (12378 - 1) /
            envelopeGap 12378 (61 / 100) 161 (17 / (100 * 12378)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12378

namespace BstLean.Part266.Row12378
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12378 161 ≤ (4886595893 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12378 161 ≤ (1630251323 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (391831523 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12378 161 ≤ (1980027237 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12378 161 ≤ (140875161 / 10000000000000000000)
  w2 : (tableEnvelope C).w2 12378 161 ≤ (32170197 / 6250000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (514717057 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (514717057 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1663328697 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3145705021 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3705947 / 1000000000) : ℝ) ≤ √(17 / (100 * 12378) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12378) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2268737661 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (8156785389 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12378) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12378) ≤ (114252187 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12378) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12378 * (161 : ℝ) ^ 2 + 26 / (10 * 12378) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12378) : ℝ)) (tA 12378 * 161 ^ 2 + 26 / (10 * 12378)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3705947 / 1000000000))) * ((514717057 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3705947 / 1000000000)) ^ 3) * ((1663328697 / 1000000000000000000000000))) + ((3145705021 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3705947 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12378) : ℝ)) d.D d.V d.P (√(tA 12378) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3705947 / 1000000000)) ^ 2 * (((2268737661 / 1000000000000000)) * ((8156785389 / 200000000000000000)))) + ((3145705021 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12378) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3705947 / 1000000000)) * ((514717057 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12378) : ℝ)) (tA 12378 * 161 ^ 2 + 26 / (10 * 12378)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((514717057 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3705947 / 1000000000)) ^ 2) * ((1663328697 / 1000000000000000000000000)) + ((3145705021 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12378) : ℝ)) (√(26 / (10 * 12378) : ℝ)) d.D d.V d.P (√(tA 12378) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3705947 / 1000000000)) * (((2268737661 / 1000000000000000)) * ((8156785389 / 200000000000000000))) + ((3145705021 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12378) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((514717057 / 100000000000000000000) : ℝ) + ((3145705021 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12378

namespace BstLean.Part266.Row12378
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12378 161 ∧
    0 ≤ (tableEnvelope C).f1 12378 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12378 161 ∧
    0 ≤ (tableEnvelope C).w1 12378 161 ∧ 0 ≤ (tableEnvelope C).w2 12378 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12378 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12378 161 ∧ 0 ≤ d.f1 12378 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12378 161 ∧ 0 ≤ d.w1 12378 161 ∧ 0 ≤ d.w2 12378 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12378 ≤ 2 * (228 / 100 : ℝ) / 12378 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12378 ≤ 2 * (370 / 100 : ℝ) / 12378 := by
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
    (completeRAData (tableEnvelope C) 12378 161).locationBound 12378 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12378 161).energyBound 12378 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12378 161) (d.f1 12378 161) d.f2 ≤
      32 * (((4886595893 / 1000000000000000000) : ℝ) + (1630251323 / 1000000000000000000) + (391831523 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12378 161) (d.w1 12378 161)
      (d.w2 12378 161) ≤
      32 * (((1980027237 / 100000000000000000000) : ℝ) + (140875161 / 10000000000000000000) + (32170197 / 6250000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12378 161) (d.f1 12378 161) d.f2 ≤
      ((4886595893 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4886595893 / 1000000000000000000)) * ((1630251323 / 1000000000000000000)) * (126 / 100) +
      2 * (((1630251323 / 1000000000000000000)) ^ 2 + 2 * ((4886595893 / 1000000000000000000)) * ((391831523 / 1000000000000000000))) +
      6 * ((1630251323 / 1000000000000000000)) * ((391831523 / 1000000000000000000)) * (126 / 100) + 8 * ((391831523 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12378 161) (d.f1 12378 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12378 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12378 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12378 161) (d.f1 12378 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12378 161) (d.w1 12378 161) (d.w2 12378 161)
  have hwexpr0 : 0 ≤ d.w0 12378 161 + d.w1 12378 161 * √(π / 2) +
      2 * d.w2 12378 161 + energyR16 12378 *
      radiusPolynomialRoot16 (d.w0 12378 161) (d.w1 12378 161) (d.w2 12378 161) := by
    positivity
  constructor
  · change (12378 : ℝ) ^ 8 * (mA 12378 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12378 161) (d.f1 12378 161) d.f2 + locationR16 12378 *
        radiusPolynomialRoot16 (d.f0 12378 161) (d.f1 12378 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12378 : ℝ) ^ 8 * (mA 12378 : ℝ) ^ 8 *
        ((((4886595893 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4886595893 / 1000000000000000000)) * ((1630251323 / 1000000000000000000)) * (126 / 100) +
          2 * (((1630251323 / 1000000000000000000)) ^ 2 + 2 * ((4886595893 / 1000000000000000000)) * ((391831523 / 1000000000000000000))) +
          6 * ((1630251323 / 1000000000000000000)) * ((391831523 / 1000000000000000000)) * (126 / 100) + 8 * ((391831523 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12378) *
          (32 * (((4886595893 / 1000000000000000000) : ℝ) + (1630251323 / 1000000000000000000) + (391831523 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12378 : ℝ) ^ 16 *
      (d.w0 12378 161 + d.w1 12378 161 * √(π / 2) + 2 * d.w2 12378 161 +
        energyR16 12378 * radiusPolynomialRoot16 (d.w0 12378 161) (d.w1 12378 161)
          (d.w2 12378 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12378 : ℝ) ^ 16 *
        (((1980027237 / 100000000000000000000) : ℝ) + ((140875161 / 10000000000000000000)) * (126 / 100) + 2 * ((32170197 / 6250000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12378) *
          (32 * (((1980027237 / 100000000000000000000) : ℝ) + (140875161 / 10000000000000000000) + (32170197 / 6250000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12378

/-! A coarse bound on the actual paper statistics constant at dimension 12379. -/
namespace BstLean.Part266.Row12379
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12377 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12377 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12377 128 ≤ (12631 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12631 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12379) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12379 : ℕ))
    (by norm_num : (12379 : ℕ) ≤ 16384)
  have ht : paperTail256 12379 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12379 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12379 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12379 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12379 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12379 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12377 128 * √(2 / (12379 : ℝ)) *
      (√(12379 : ℝ) + paperT0 12379 + paperTail256 12379) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12379 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12379 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12379 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12377 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12377 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12379 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12379

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12379
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12379 (61 / 100) 161 (17 / (100 * 12379)) (26 / (10 * 12379)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12379 (61 / 100) 161 (17 / (100 * 12379)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (514592321 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (207848909 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (157182617 / 25000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12379 / 12379 * (61 / 100)) ^ 4 * inverseRadius8 (12379 - 1) /
            envelopeGap 12379 (61 / 100) 161 (17 / (100 * 12379)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12379

namespace BstLean.Part266.Row12379
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12379 161 ≤ (1221402549 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12379 161 ≤ (1629922357 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (391752423 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12379 161 ≤ (1979547643 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12379 161 ≤ (1408410331 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12379 161 ≤ (128649603 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (514592321 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (514592321 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (207848909 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (157182617 / 25000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3705797 / 1000000000) : ℝ) ≤ √(17 / (100 * 12379) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12379) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1134231371 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (20388668863 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12379) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12379) ≤ (114242957 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12379) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12379 * (161 : ℝ) ^ 2 + 26 / (10 * 12379) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12379) : ℝ)) (tA 12379 * 161 ^ 2 + 26 / (10 * 12379)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3705797 / 1000000000))) * ((514592321 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3705797 / 1000000000)) ^ 3) * ((207848909 / 125000000000000000000000))) + ((157182617 / 25000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3705797 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12379) : ℝ)) d.D d.V d.P (√(tA 12379) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3705797 / 1000000000)) ^ 2 * (((1134231371 / 500000000000000)) * ((20388668863 / 500000000000000000)))) + ((157182617 / 25000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12379) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3705797 / 1000000000)) * ((514592321 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12379) : ℝ)) (tA 12379 * 161 ^ 2 + 26 / (10 * 12379)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((514592321 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3705797 / 1000000000)) ^ 2) * ((207848909 / 125000000000000000000000)) + ((157182617 / 25000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12379) : ℝ)) (√(26 / (10 * 12379) : ℝ)) d.D d.V d.P (√(tA 12379) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3705797 / 1000000000)) * (((1134231371 / 500000000000000)) * ((20388668863 / 500000000000000000))) + ((157182617 / 25000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12379) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((514592321 / 100000000000000000000) : ℝ) + ((157182617 / 25000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12379

namespace BstLean.Part266.Row12379
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12379 161 ∧
    0 ≤ (tableEnvelope C).f1 12379 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12379 161 ∧
    0 ≤ (tableEnvelope C).w1 12379 161 ∧ 0 ≤ (tableEnvelope C).w2 12379 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12379 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12379 161 ∧ 0 ≤ d.f1 12379 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12379 161 ∧ 0 ≤ d.w1 12379 161 ∧ 0 ≤ d.w2 12379 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12379 ≤ 2 * (228 / 100 : ℝ) / 12379 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12379 ≤ 2 * (370 / 100 : ℝ) / 12379 := by
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
    (completeRAData (tableEnvelope C) 12379 161).locationBound 12379 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12379 161).energyBound 12379 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12379 161) (d.f1 12379 161) d.f2 ≤
      32 * (((1221402549 / 250000000000000000) : ℝ) + (1629922357 / 1000000000000000000) + (391752423 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12379 161) (d.w1 12379 161)
      (d.w2 12379 161) ≤
      32 * (((1979547643 / 100000000000000000000) : ℝ) + (1408410331 / 100000000000000000000) + (128649603 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12379 161) (d.f1 12379 161) d.f2 ≤
      ((1221402549 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1221402549 / 250000000000000000)) * ((1629922357 / 1000000000000000000)) * (126 / 100) +
      2 * (((1629922357 / 1000000000000000000)) ^ 2 + 2 * ((1221402549 / 250000000000000000)) * ((391752423 / 1000000000000000000))) +
      6 * ((1629922357 / 1000000000000000000)) * ((391752423 / 1000000000000000000)) * (126 / 100) + 8 * ((391752423 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12379 161) (d.f1 12379 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12379 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12379 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12379 161) (d.f1 12379 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12379 161) (d.w1 12379 161) (d.w2 12379 161)
  have hwexpr0 : 0 ≤ d.w0 12379 161 + d.w1 12379 161 * √(π / 2) +
      2 * d.w2 12379 161 + energyR16 12379 *
      radiusPolynomialRoot16 (d.w0 12379 161) (d.w1 12379 161) (d.w2 12379 161) := by
    positivity
  constructor
  · change (12379 : ℝ) ^ 8 * (mA 12379 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12379 161) (d.f1 12379 161) d.f2 + locationR16 12379 *
        radiusPolynomialRoot16 (d.f0 12379 161) (d.f1 12379 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12379 : ℝ) ^ 8 * (mA 12379 : ℝ) ^ 8 *
        ((((1221402549 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1221402549 / 250000000000000000)) * ((1629922357 / 1000000000000000000)) * (126 / 100) +
          2 * (((1629922357 / 1000000000000000000)) ^ 2 + 2 * ((1221402549 / 250000000000000000)) * ((391752423 / 1000000000000000000))) +
          6 * ((1629922357 / 1000000000000000000)) * ((391752423 / 1000000000000000000)) * (126 / 100) + 8 * ((391752423 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12379) *
          (32 * (((1221402549 / 250000000000000000) : ℝ) + (1629922357 / 1000000000000000000) + (391752423 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12379 : ℝ) ^ 16 *
      (d.w0 12379 161 + d.w1 12379 161 * √(π / 2) + 2 * d.w2 12379 161 +
        energyR16 12379 * radiusPolynomialRoot16 (d.w0 12379 161) (d.w1 12379 161)
          (d.w2 12379 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12379 : ℝ) ^ 16 *
        (((1979547643 / 100000000000000000000) : ℝ) + ((1408410331 / 100000000000000000000)) * (126 / 100) + 2 * ((128649603 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12379) *
          (32 * (((1979547643 / 100000000000000000000) : ℝ) + (1408410331 / 100000000000000000000) + (128649603 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12379

/-! A coarse bound on the actual paper statistics constant at dimension 12380. -/
namespace BstLean.Part266.Row12380
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12378 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12378 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12378 128 ≤ (12632 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12632 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12380) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12380 : ℕ))
    (by norm_num : (12380 : ℕ) ≤ 16384)
  have ht : paperTail256 12380 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12380 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12380 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12380 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12380 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12380 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12378 128 * √(2 / (12380 : ℝ)) *
      (√(12380 : ℝ) + paperT0 12380 + paperTail256 12380) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12380 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12380 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12380 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12378 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12378 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12380 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12380

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12380
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12380 (61 / 100) 161 (17 / (100 * 12380)) (26 / (10 * 12380)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12380 (61 / 100) 161 (17 / (100 * 12380)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (4115741 / 800000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (332450813 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3141601167 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12380 / 12380 * (61 / 100)) ^ 4 * inverseRadius8 (12380 - 1) /
            envelopeGap 12380 (61 / 100) 161 (17 / (100 * 12380)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12380

namespace BstLean.Part266.Row12380
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12380 161 ≤ (4884624849 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12380 161 ≤ (3259187 / 2000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (97918337 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12380 161 ≤ (1979068219 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12380 161 ≤ (140806917 / 10000000000000000000)
  w2 : (tableEnvelope C).w2 12380 161 ≤ (32154607 / 6250000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (4115741 / 800000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (4115741 / 800000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (332450813 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3141601167 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3705647 / 1000000000) : ℝ) ≤ √(17 / (100 * 12380) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12380) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2268187879 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (10192687529 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12380) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12380) ≤ (114233729 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12380) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12380 * (161 : ℝ) ^ 2 + 26 / (10 * 12380) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12380) : ℝ)) (tA 12380 * 161 ^ 2 + 26 / (10 * 12380)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3705647 / 1000000000))) * ((4115741 / 800000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3705647 / 1000000000)) ^ 3) * ((332450813 / 200000000000000000000000))) + ((3141601167 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3705647 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12380) : ℝ)) d.D d.V d.P (√(tA 12380) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3705647 / 1000000000)) ^ 2 * (((2268187879 / 1000000000000000)) * ((10192687529 / 250000000000000000)))) + ((3141601167 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12380) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3705647 / 1000000000)) * ((4115741 / 800000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12380) : ℝ)) (tA 12380 * 161 ^ 2 + 26 / (10 * 12380)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((4115741 / 800000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3705647 / 1000000000)) ^ 2) * ((332450813 / 200000000000000000000000)) + ((3141601167 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12380) : ℝ)) (√(26 / (10 * 12380) : ℝ)) d.D d.V d.P (√(tA 12380) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3705647 / 1000000000)) * (((2268187879 / 1000000000000000)) * ((10192687529 / 250000000000000000))) + ((3141601167 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12380) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((4115741 / 800000000000000000) : ℝ) + ((3141601167 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12380

namespace BstLean.Part266.Row12380
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12380 161 ∧
    0 ≤ (tableEnvelope C).f1 12380 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12380 161 ∧
    0 ≤ (tableEnvelope C).w1 12380 161 ∧ 0 ≤ (tableEnvelope C).w2 12380 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12380 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12380 161 ∧ 0 ≤ d.f1 12380 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12380 161 ∧ 0 ≤ d.w1 12380 161 ∧ 0 ≤ d.w2 12380 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12380 ≤ 2 * (228 / 100 : ℝ) / 12380 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12380 ≤ 2 * (370 / 100 : ℝ) / 12380 := by
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
    (completeRAData (tableEnvelope C) 12380 161).locationBound 12380 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12380 161).energyBound 12380 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12380 161) (d.f1 12380 161) d.f2 ≤
      32 * (((4884624849 / 1000000000000000000) : ℝ) + (3259187 / 2000000000000000) + (97918337 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12380 161) (d.w1 12380 161)
      (d.w2 12380 161) ≤
      32 * (((1979068219 / 100000000000000000000) : ℝ) + (140806917 / 10000000000000000000) + (32154607 / 6250000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12380 161) (d.f1 12380 161) d.f2 ≤
      ((4884624849 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4884624849 / 1000000000000000000)) * ((3259187 / 2000000000000000)) * (126 / 100) +
      2 * (((3259187 / 2000000000000000)) ^ 2 + 2 * ((4884624849 / 1000000000000000000)) * ((97918337 / 250000000000000000))) +
      6 * ((3259187 / 2000000000000000)) * ((97918337 / 250000000000000000)) * (126 / 100) + 8 * ((97918337 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12380 161) (d.f1 12380 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12380 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12380 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12380 161) (d.f1 12380 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12380 161) (d.w1 12380 161) (d.w2 12380 161)
  have hwexpr0 : 0 ≤ d.w0 12380 161 + d.w1 12380 161 * √(π / 2) +
      2 * d.w2 12380 161 + energyR16 12380 *
      radiusPolynomialRoot16 (d.w0 12380 161) (d.w1 12380 161) (d.w2 12380 161) := by
    positivity
  constructor
  · change (12380 : ℝ) ^ 8 * (mA 12380 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12380 161) (d.f1 12380 161) d.f2 + locationR16 12380 *
        radiusPolynomialRoot16 (d.f0 12380 161) (d.f1 12380 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12380 : ℝ) ^ 8 * (mA 12380 : ℝ) ^ 8 *
        ((((4884624849 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4884624849 / 1000000000000000000)) * ((3259187 / 2000000000000000)) * (126 / 100) +
          2 * (((3259187 / 2000000000000000)) ^ 2 + 2 * ((4884624849 / 1000000000000000000)) * ((97918337 / 250000000000000000))) +
          6 * ((3259187 / 2000000000000000)) * ((97918337 / 250000000000000000)) * (126 / 100) + 8 * ((97918337 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12380) *
          (32 * (((4884624849 / 1000000000000000000) : ℝ) + (3259187 / 2000000000000000) + (97918337 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12380 : ℝ) ^ 16 *
      (d.w0 12380 161 + d.w1 12380 161 * √(π / 2) + 2 * d.w2 12380 161 +
        energyR16 12380 * radiusPolynomialRoot16 (d.w0 12380 161) (d.w1 12380 161)
          (d.w2 12380 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12380 : ℝ) ^ 16 *
        (((1979068219 / 100000000000000000000) : ℝ) + ((140806917 / 10000000000000000000)) * (126 / 100) + 2 * ((32154607 / 6250000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12380) *
          (32 * (((1979068219 / 100000000000000000000) : ℝ) + (140806917 / 10000000000000000000) + (32154607 / 6250000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12380

/-! A coarse bound on the actual paper statistics constant at dimension 12381. -/
namespace BstLean.Part266.Row12381
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12379 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12379 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12379 128 ≤ (12633 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12633 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12381) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12381 : ℕ))
    (by norm_num : (12381 : ℕ) ≤ 16384)
  have ht : paperTail256 12381 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12381 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12381 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12381 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12381 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12381 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12379 128 * √(2 / (12381 : ℝ)) *
      (√(12381 : ℝ) + paperT0 12381 + paperTail256 12381) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12381 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12381 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12381 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12379 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12379 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12381 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12381

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12381
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12381 (61 / 100) 161 (17 / (100 * 12381)) (26 / (10 * 12381)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12381 (61 / 100) 161 (17 / (100 * 12381)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (51434297 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (830858537 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3139551501 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12381 / 12381 * (61 / 100)) ^ 4 * inverseRadius8 (12381 - 1) /
            envelopeGap 12381 (61 / 100) 161 (17 / (100 * 12381)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12381

namespace BstLean.Part266.Row12381
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12381 161 ≤ (2441818021 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12381 161 ≤ (1629263873 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (391594191 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12381 161 ≤ (1978588173 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12381 161 ≤ (1407727747 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12381 161 ≤ (514349053 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (51434297 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (51434297 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (830858537 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3139551501 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1852749 / 500000000) : ℝ) ≤ √(17 / (100 * 12381) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12381) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (141744567 / 62500000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40764164091 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12381) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12381) ≤ (114224503 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12381) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12381 * (161 : ℝ) ^ 2 + 26 / (10 * 12381) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12381) : ℝ)) (tA 12381 * 161 ^ 2 + 26 / (10 * 12381)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1852749 / 500000000))) * ((51434297 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1852749 / 500000000)) ^ 3) * ((830858537 / 500000000000000000000000))) + ((3139551501 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1852749 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12381) : ℝ)) d.D d.V d.P (√(tA 12381) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1852749 / 500000000)) ^ 2 * (((141744567 / 62500000000000)) * ((40764164091 / 1000000000000000000)))) + ((3139551501 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12381) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1852749 / 500000000)) * ((51434297 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12381) : ℝ)) (tA 12381 * 161 ^ 2 + 26 / (10 * 12381)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((51434297 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1852749 / 500000000)) ^ 2) * ((830858537 / 500000000000000000000000)) + ((3139551501 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12381) : ℝ)) (√(26 / (10 * 12381) : ℝ)) d.D d.V d.P (√(tA 12381) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1852749 / 500000000)) * (((141744567 / 62500000000000)) * ((40764164091 / 1000000000000000000))) + ((3139551501 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12381) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((51434297 / 10000000000000000000) : ℝ) + ((3139551501 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12381

namespace BstLean.Part266.Row12381
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12381 161 ∧
    0 ≤ (tableEnvelope C).f1 12381 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12381 161 ∧
    0 ≤ (tableEnvelope C).w1 12381 161 ∧ 0 ≤ (tableEnvelope C).w2 12381 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12381 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12381 161 ∧ 0 ≤ d.f1 12381 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12381 161 ∧ 0 ≤ d.w1 12381 161 ∧ 0 ≤ d.w2 12381 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12381 ≤ 2 * (228 / 100 : ℝ) / 12381 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12381 ≤ 2 * (370 / 100 : ℝ) / 12381 := by
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
    (completeRAData (tableEnvelope C) 12381 161).locationBound 12381 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12381 161).energyBound 12381 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12381 161) (d.f1 12381 161) d.f2 ≤
      32 * (((2441818021 / 500000000000000000) : ℝ) + (1629263873 / 1000000000000000000) + (391594191 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12381 161) (d.w1 12381 161)
      (d.w2 12381 161) ≤
      32 * (((1978588173 / 100000000000000000000) : ℝ) + (1407727747 / 100000000000000000000) + (514349053 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12381 161) (d.f1 12381 161) d.f2 ≤
      ((2441818021 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2441818021 / 500000000000000000)) * ((1629263873 / 1000000000000000000)) * (126 / 100) +
      2 * (((1629263873 / 1000000000000000000)) ^ 2 + 2 * ((2441818021 / 500000000000000000)) * ((391594191 / 1000000000000000000))) +
      6 * ((1629263873 / 1000000000000000000)) * ((391594191 / 1000000000000000000)) * (126 / 100) + 8 * ((391594191 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12381 161) (d.f1 12381 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12381 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12381 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12381 161) (d.f1 12381 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12381 161) (d.w1 12381 161) (d.w2 12381 161)
  have hwexpr0 : 0 ≤ d.w0 12381 161 + d.w1 12381 161 * √(π / 2) +
      2 * d.w2 12381 161 + energyR16 12381 *
      radiusPolynomialRoot16 (d.w0 12381 161) (d.w1 12381 161) (d.w2 12381 161) := by
    positivity
  constructor
  · change (12381 : ℝ) ^ 8 * (mA 12381 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12381 161) (d.f1 12381 161) d.f2 + locationR16 12381 *
        radiusPolynomialRoot16 (d.f0 12381 161) (d.f1 12381 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12381 : ℝ) ^ 8 * (mA 12381 : ℝ) ^ 8 *
        ((((2441818021 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2441818021 / 500000000000000000)) * ((1629263873 / 1000000000000000000)) * (126 / 100) +
          2 * (((1629263873 / 1000000000000000000)) ^ 2 + 2 * ((2441818021 / 500000000000000000)) * ((391594191 / 1000000000000000000))) +
          6 * ((1629263873 / 1000000000000000000)) * ((391594191 / 1000000000000000000)) * (126 / 100) + 8 * ((391594191 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12381) *
          (32 * (((2441818021 / 500000000000000000) : ℝ) + (1629263873 / 1000000000000000000) + (391594191 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12381 : ℝ) ^ 16 *
      (d.w0 12381 161 + d.w1 12381 161 * √(π / 2) + 2 * d.w2 12381 161 +
        energyR16 12381 * radiusPolynomialRoot16 (d.w0 12381 161) (d.w1 12381 161)
          (d.w2 12381 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12381 : ℝ) ^ 16 *
        (((1978588173 / 100000000000000000000) : ℝ) + ((1407727747 / 100000000000000000000)) * (126 / 100) + 2 * ((514349053 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12381) *
          (32 * (((1978588173 / 100000000000000000000) : ℝ) + (1407727747 / 100000000000000000000) + (514349053 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12381

/-! A coarse bound on the actual paper statistics constant at dimension 12382. -/
namespace BstLean.Part266.Row12382
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12380 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12380 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12380 128 ≤ (12634 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12634 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12382) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12382 : ℕ))
    (by norm_num : (12382 : ℕ) ≤ 16384)
  have ht : paperTail256 12382 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12382 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12382 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12382 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12382 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12382 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12380 128 * √(2 / (12382 : ℝ)) *
      (√(12382 : ℝ) + paperT0 12382 + paperTail256 12382) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12382 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12382 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12382 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12380 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12380 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12382 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12382

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12382
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12382 (61 / 100) 161 (17 / (100 * 12382)) (26 / (10 * 12382)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12382 (61 / 100) 161 (17 / (100 * 12382)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (257109177 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1661180301 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6275006683 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12382 / 12382 * (61 / 100)) ^ 4 * inverseRadius8 (12382 - 1) /
            envelopeGap 12382 (61 / 100) 161 (17 / (100 * 12382)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12382

namespace BstLean.Part266.Row12382
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12382 161 ≤ (4882651391 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12382 161 ≤ (1628935233 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (97878791 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12382 161 ≤ (1978109087 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12382 161 ≤ (1407386819 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12382 161 ≤ (514224433 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (257109177 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (257109177 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1661180301 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6275006683 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((926337 / 250000000) : ℝ) ≤ √(17 / (100 * 12382) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12382) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1133819159 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (10189394919 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12382) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12382) ≤ (57107639 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12382) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12382 * (161 : ℝ) ^ 2 + 26 / (10 * 12382) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12382) : ℝ)) (tA 12382 * 161 ^ 2 + 26 / (10 * 12382)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((926337 / 250000000))) * ((257109177 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((926337 / 250000000)) ^ 3) * ((1661180301 / 1000000000000000000000000))) + ((6275006683 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((926337 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12382) : ℝ)) d.D d.V d.P (√(tA 12382) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((926337 / 250000000)) ^ 2 * (((1133819159 / 500000000000000)) * ((10189394919 / 250000000000000000)))) + ((6275006683 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12382) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((926337 / 250000000)) * ((257109177 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12382) : ℝ)) (tA 12382 * 161 ^ 2 + 26 / (10 * 12382)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((257109177 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((926337 / 250000000)) ^ 2) * ((1661180301 / 1000000000000000000000000)) + ((6275006683 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12382) : ℝ)) (√(26 / (10 * 12382) : ℝ)) d.D d.V d.P (√(tA 12382) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((926337 / 250000000)) * (((1133819159 / 500000000000000)) * ((10189394919 / 250000000000000000))) + ((6275006683 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12382) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((257109177 / 50000000000000000000) : ℝ) + ((6275006683 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12382

namespace BstLean.Part266.Row12382
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12382 161 ∧
    0 ≤ (tableEnvelope C).f1 12382 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12382 161 ∧
    0 ≤ (tableEnvelope C).w1 12382 161 ∧ 0 ≤ (tableEnvelope C).w2 12382 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12382 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12382 161 ∧ 0 ≤ d.f1 12382 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12382 161 ∧ 0 ≤ d.w1 12382 161 ∧ 0 ≤ d.w2 12382 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12382 ≤ 2 * (228 / 100 : ℝ) / 12382 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12382 ≤ 2 * (370 / 100 : ℝ) / 12382 := by
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
    (completeRAData (tableEnvelope C) 12382 161).locationBound 12382 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12382 161).energyBound 12382 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12382 161) (d.f1 12382 161) d.f2 ≤
      32 * (((4882651391 / 1000000000000000000) : ℝ) + (1628935233 / 1000000000000000000) + (97878791 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12382 161) (d.w1 12382 161)
      (d.w2 12382 161) ≤
      32 * (((1978109087 / 100000000000000000000) : ℝ) + (1407386819 / 100000000000000000000) + (514224433 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12382 161) (d.f1 12382 161) d.f2 ≤
      ((4882651391 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4882651391 / 1000000000000000000)) * ((1628935233 / 1000000000000000000)) * (126 / 100) +
      2 * (((1628935233 / 1000000000000000000)) ^ 2 + 2 * ((4882651391 / 1000000000000000000)) * ((97878791 / 250000000000000000))) +
      6 * ((1628935233 / 1000000000000000000)) * ((97878791 / 250000000000000000)) * (126 / 100) + 8 * ((97878791 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12382 161) (d.f1 12382 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12382 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12382 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12382 161) (d.f1 12382 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12382 161) (d.w1 12382 161) (d.w2 12382 161)
  have hwexpr0 : 0 ≤ d.w0 12382 161 + d.w1 12382 161 * √(π / 2) +
      2 * d.w2 12382 161 + energyR16 12382 *
      radiusPolynomialRoot16 (d.w0 12382 161) (d.w1 12382 161) (d.w2 12382 161) := by
    positivity
  constructor
  · change (12382 : ℝ) ^ 8 * (mA 12382 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12382 161) (d.f1 12382 161) d.f2 + locationR16 12382 *
        radiusPolynomialRoot16 (d.f0 12382 161) (d.f1 12382 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12382 : ℝ) ^ 8 * (mA 12382 : ℝ) ^ 8 *
        ((((4882651391 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4882651391 / 1000000000000000000)) * ((1628935233 / 1000000000000000000)) * (126 / 100) +
          2 * (((1628935233 / 1000000000000000000)) ^ 2 + 2 * ((4882651391 / 1000000000000000000)) * ((97878791 / 250000000000000000))) +
          6 * ((1628935233 / 1000000000000000000)) * ((97878791 / 250000000000000000)) * (126 / 100) + 8 * ((97878791 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12382) *
          (32 * (((4882651391 / 1000000000000000000) : ℝ) + (1628935233 / 1000000000000000000) + (97878791 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12382 : ℝ) ^ 16 *
      (d.w0 12382 161 + d.w1 12382 161 * √(π / 2) + 2 * d.w2 12382 161 +
        energyR16 12382 * radiusPolynomialRoot16 (d.w0 12382 161) (d.w1 12382 161)
          (d.w2 12382 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12382 : ℝ) ^ 16 *
        (((1978109087 / 100000000000000000000) : ℝ) + ((1407386819 / 100000000000000000000)) * (126 / 100) + 2 * ((514224433 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12382) *
          (32 * (((1978109087 / 100000000000000000000) : ℝ) + (1407386819 / 100000000000000000000) + (514224433 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12382

/-! A coarse bound on the actual paper statistics constant at dimension 12383. -/
namespace BstLean.Part266.Row12383
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12381 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12381 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12381 128 ≤ (12635 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12635 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12383) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12383 : ℕ))
    (by norm_num : (12383 : ℕ) ≤ 16384)
  have ht : paperTail256 12383 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12383 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12383 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12383 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12383 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12383 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12381 128 * √(2 / (12383 : ℝ)) *
      (√(12383 : ℝ) + paperT0 12383 + paperTail256 12383) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12383 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12383 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12383 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12381 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12381 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12383 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12383

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12383
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12383 (61 / 100) 161 (17 / (100 * 12383)) (26 / (10 * 12383)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12383 (61 / 100) 161 (17 / (100 * 12383)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (514093779 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (51895117 / 31250000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1567728343 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12383 / 12383 * (61 / 100)) ^ 4 * inverseRadius8 (12383 - 1) /
            envelopeGap 12383 (61 / 100) 161 (17 / (100 * 12383)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12383

namespace BstLean.Part266.Row12383
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12383 161 ≤ (976333417 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12383 161 ≤ (1628606703 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (391436161 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12383 161 ≤ (197763017 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 12383 161 ≤ (1407046009 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12383 161 ≤ (257049927 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (514093779 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (514093779 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (51895117 / 31250000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1567728343 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1852599 / 500000000) : ℝ) ≤ √(17 / (100 * 12383) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12383) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1133681811 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40750996847 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12383) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12383) ≤ (57103027 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12383) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12383 * (161 : ℝ) ^ 2 + 26 / (10 * 12383) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12383) : ℝ)) (tA 12383 * 161 ^ 2 + 26 / (10 * 12383)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1852599 / 500000000))) * ((514093779 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1852599 / 500000000)) ^ 3) * ((51895117 / 31250000000000000000000))) + ((1567728343 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1852599 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12383) : ℝ)) d.D d.V d.P (√(tA 12383) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1852599 / 500000000)) ^ 2 * (((1133681811 / 500000000000000)) * ((40750996847 / 1000000000000000000)))) + ((1567728343 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12383) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1852599 / 500000000)) * ((514093779 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12383) : ℝ)) (tA 12383 * 161 ^ 2 + 26 / (10 * 12383)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((514093779 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1852599 / 500000000)) ^ 2) * ((51895117 / 31250000000000000000000)) + ((1567728343 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12383) : ℝ)) (√(26 / (10 * 12383) : ℝ)) d.D d.V d.P (√(tA 12383) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1852599 / 500000000)) * (((1133681811 / 500000000000000)) * ((40750996847 / 1000000000000000000))) + ((1567728343 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12383) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((514093779 / 100000000000000000000) : ℝ) + ((1567728343 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12383

namespace BstLean.Part266.Row12383
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12383 161 ∧
    0 ≤ (tableEnvelope C).f1 12383 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12383 161 ∧
    0 ≤ (tableEnvelope C).w1 12383 161 ∧ 0 ≤ (tableEnvelope C).w2 12383 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12383 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12383 161 ∧ 0 ≤ d.f1 12383 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12383 161 ∧ 0 ≤ d.w1 12383 161 ∧ 0 ≤ d.w2 12383 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12383 ≤ 2 * (228 / 100 : ℝ) / 12383 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12383 ≤ 2 * (370 / 100 : ℝ) / 12383 := by
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
    (completeRAData (tableEnvelope C) 12383 161).locationBound 12383 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12383 161).energyBound 12383 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12383 161) (d.f1 12383 161) d.f2 ≤
      32 * (((976333417 / 200000000000000000) : ℝ) + (1628606703 / 1000000000000000000) + (391436161 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12383 161) (d.w1 12383 161)
      (d.w2 12383 161) ≤
      32 * (((197763017 / 10000000000000000000) : ℝ) + (1407046009 / 100000000000000000000) + (257049927 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12383 161) (d.f1 12383 161) d.f2 ≤
      ((976333417 / 200000000000000000) : ℝ) ^ 2 + 2 * ((976333417 / 200000000000000000)) * ((1628606703 / 1000000000000000000)) * (126 / 100) +
      2 * (((1628606703 / 1000000000000000000)) ^ 2 + 2 * ((976333417 / 200000000000000000)) * ((391436161 / 1000000000000000000))) +
      6 * ((1628606703 / 1000000000000000000)) * ((391436161 / 1000000000000000000)) * (126 / 100) + 8 * ((391436161 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12383 161) (d.f1 12383 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12383 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12383 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12383 161) (d.f1 12383 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12383 161) (d.w1 12383 161) (d.w2 12383 161)
  have hwexpr0 : 0 ≤ d.w0 12383 161 + d.w1 12383 161 * √(π / 2) +
      2 * d.w2 12383 161 + energyR16 12383 *
      radiusPolynomialRoot16 (d.w0 12383 161) (d.w1 12383 161) (d.w2 12383 161) := by
    positivity
  constructor
  · change (12383 : ℝ) ^ 8 * (mA 12383 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12383 161) (d.f1 12383 161) d.f2 + locationR16 12383 *
        radiusPolynomialRoot16 (d.f0 12383 161) (d.f1 12383 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12383 : ℝ) ^ 8 * (mA 12383 : ℝ) ^ 8 *
        ((((976333417 / 200000000000000000) : ℝ) ^ 2 + 2 * ((976333417 / 200000000000000000)) * ((1628606703 / 1000000000000000000)) * (126 / 100) +
          2 * (((1628606703 / 1000000000000000000)) ^ 2 + 2 * ((976333417 / 200000000000000000)) * ((391436161 / 1000000000000000000))) +
          6 * ((1628606703 / 1000000000000000000)) * ((391436161 / 1000000000000000000)) * (126 / 100) + 8 * ((391436161 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12383) *
          (32 * (((976333417 / 200000000000000000) : ℝ) + (1628606703 / 1000000000000000000) + (391436161 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12383 : ℝ) ^ 16 *
      (d.w0 12383 161 + d.w1 12383 161 * √(π / 2) + 2 * d.w2 12383 161 +
        energyR16 12383 * radiusPolynomialRoot16 (d.w0 12383 161) (d.w1 12383 161)
          (d.w2 12383 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12383 : ℝ) ^ 16 *
        (((197763017 / 10000000000000000000) : ℝ) + ((1407046009 / 100000000000000000000)) * (126 / 100) + 2 * ((257049927 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12383) *
          (32 * (((197763017 / 10000000000000000000) : ℝ) + (1407046009 / 100000000000000000000) + (257049927 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12383

/-! A coarse bound on the actual paper statistics constant at dimension 12384. -/
namespace BstLean.Part266.Row12384
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12382 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12382 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12382 128 ≤ (12636 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12636 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12384) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12384 : ℕ))
    (by norm_num : (12384 : ℕ) ≤ 16384)
  have ht : paperTail256 12384 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12384 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12384 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12384 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12384 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12384 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12382 128 * √(2 / (12384 : ℝ)) *
      (√(12384 : ℝ) + paperT0 12384 + paperTail256 12384) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12384 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12384 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12384 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12382 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12382 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12384 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12384

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12384
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12384 (61 / 100) 161 (17 / (100 * 12384)) (26 / (10 * 12384)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12384 (61 / 100) 161 (17 / (100 * 12384)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (128492311 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1660107403 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6266823069 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12384 / 12384 * (61 / 100)) ^ 4 * inverseRadius8 (12384 - 1) /
            envelopeGap 12384 (61 / 100) 161 (17 / (100 * 12384)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12384

namespace BstLean.Part266.Row12384
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12384 161 ≤ (4880679321 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12384 161 ≤ (814138701 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (391357077 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12384 161 ≤ (1977150631 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12384 161 ≤ (175838117 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 12384 161 ≤ (102795063 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (128492311 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (128492311 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1660107403 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6266823069 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3705049 / 1000000000) : ℝ) ≤ √(17 / (100 * 12384) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12384) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (113354449 / 50000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (20372207803 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12384) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12384) ≤ (3568651 / 31250000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12384) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12384 * (161 : ℝ) ^ 2 + 26 / (10 * 12384) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12384) : ℝ)) (tA 12384 * 161 ^ 2 + 26 / (10 * 12384)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3705049 / 1000000000))) * ((128492311 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3705049 / 1000000000)) ^ 3) * ((1660107403 / 1000000000000000000000000))) + ((6266823069 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3705049 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12384) : ℝ)) d.D d.V d.P (√(tA 12384) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3705049 / 1000000000)) ^ 2 * (((113354449 / 50000000000000)) * ((20372207803 / 500000000000000000)))) + ((6266823069 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12384) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3705049 / 1000000000)) * ((128492311 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12384) : ℝ)) (tA 12384 * 161 ^ 2 + 26 / (10 * 12384)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((128492311 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3705049 / 1000000000)) ^ 2) * ((1660107403 / 1000000000000000000000000)) + ((6266823069 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12384) : ℝ)) (√(26 / (10 * 12384) : ℝ)) d.D d.V d.P (√(tA 12384) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3705049 / 1000000000)) * (((113354449 / 50000000000000)) * ((20372207803 / 500000000000000000))) + ((6266823069 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12384) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((128492311 / 25000000000000000000) : ℝ) + ((6266823069 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12384

namespace BstLean.Part266.Row12384
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12384 161 ∧
    0 ≤ (tableEnvelope C).f1 12384 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12384 161 ∧
    0 ≤ (tableEnvelope C).w1 12384 161 ∧ 0 ≤ (tableEnvelope C).w2 12384 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12384 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12384 161 ∧ 0 ≤ d.f1 12384 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12384 161 ∧ 0 ≤ d.w1 12384 161 ∧ 0 ≤ d.w2 12384 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12384 ≤ 2 * (228 / 100 : ℝ) / 12384 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12384 ≤ 2 * (370 / 100 : ℝ) / 12384 := by
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
    (completeRAData (tableEnvelope C) 12384 161).locationBound 12384 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12384 161).energyBound 12384 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12384 161) (d.f1 12384 161) d.f2 ≤
      32 * (((4880679321 / 1000000000000000000) : ℝ) + (814138701 / 500000000000000000) + (391357077 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12384 161) (d.w1 12384 161)
      (d.w2 12384 161) ≤
      32 * (((1977150631 / 100000000000000000000) : ℝ) + (175838117 / 12500000000000000000) + (102795063 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12384 161) (d.f1 12384 161) d.f2 ≤
      ((4880679321 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4880679321 / 1000000000000000000)) * ((814138701 / 500000000000000000)) * (126 / 100) +
      2 * (((814138701 / 500000000000000000)) ^ 2 + 2 * ((4880679321 / 1000000000000000000)) * ((391357077 / 1000000000000000000))) +
      6 * ((814138701 / 500000000000000000)) * ((391357077 / 1000000000000000000)) * (126 / 100) + 8 * ((391357077 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12384 161) (d.f1 12384 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12384 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12384 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12384 161) (d.f1 12384 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12384 161) (d.w1 12384 161) (d.w2 12384 161)
  have hwexpr0 : 0 ≤ d.w0 12384 161 + d.w1 12384 161 * √(π / 2) +
      2 * d.w2 12384 161 + energyR16 12384 *
      radiusPolynomialRoot16 (d.w0 12384 161) (d.w1 12384 161) (d.w2 12384 161) := by
    positivity
  constructor
  · change (12384 : ℝ) ^ 8 * (mA 12384 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12384 161) (d.f1 12384 161) d.f2 + locationR16 12384 *
        radiusPolynomialRoot16 (d.f0 12384 161) (d.f1 12384 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12384 : ℝ) ^ 8 * (mA 12384 : ℝ) ^ 8 *
        ((((4880679321 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4880679321 / 1000000000000000000)) * ((814138701 / 500000000000000000)) * (126 / 100) +
          2 * (((814138701 / 500000000000000000)) ^ 2 + 2 * ((4880679321 / 1000000000000000000)) * ((391357077 / 1000000000000000000))) +
          6 * ((814138701 / 500000000000000000)) * ((391357077 / 1000000000000000000)) * (126 / 100) + 8 * ((391357077 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12384) *
          (32 * (((4880679321 / 1000000000000000000) : ℝ) + (814138701 / 500000000000000000) + (391357077 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12384 : ℝ) ^ 16 *
      (d.w0 12384 161 + d.w1 12384 161 * √(π / 2) + 2 * d.w2 12384 161 +
        energyR16 12384 * radiusPolynomialRoot16 (d.w0 12384 161) (d.w1 12384 161)
          (d.w2 12384 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12384 : ℝ) ^ 16 *
        (((1977150631 / 100000000000000000000) : ℝ) + ((175838117 / 12500000000000000000)) * (126 / 100) + 2 * ((102795063 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12384) *
          (32 * (((1977150631 / 100000000000000000000) : ℝ) + (175838117 / 12500000000000000000) + (102795063 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12384

/-! A coarse bound on the actual paper statistics constant at dimension 12385. -/
namespace BstLean.Part266.Row12385
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12383 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12383 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12383 128 ≤ (12637 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12637 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12385) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12385 : ℕ))
    (by norm_num : (12385 : ℕ) ≤ 16384)
  have ht : paperTail256 12385 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12385 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12385 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12385 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12385 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12385 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12383 128 * √(2 / (12385 : ℝ)) *
      (√(12385 : ℝ) + paperT0 12385 + paperTail256 12385) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12385 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12385 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12385 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12383 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12383 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12385 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12385

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12385
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12385 (61 / 100) 161 (17 / (100 * 12385)) (26 / (10 * 12385)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12385 (61 / 100) 161 (17 / (100 * 12385)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (2055379 / 400000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (20744641 / 12500000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (626273577 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12385 / 12385 * (61 / 100)) ^ 4 * inverseRadius8 (12385 - 1) /
            envelopeGap 12385 (61 / 100) 161 (17 / (100 * 12385)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12385

namespace BstLean.Part266.Row12385
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12385 161 ≤ (4879695713 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12385 161 ≤ (162794909 / 100000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (391278123 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12385 161 ≤ (1976672053 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12385 161 ≤ (35159109 / 2500000000000000000)
  w2 : (tableEnvelope C).w2 12385 161 ≤ (513850817 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (2055379 / 400000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (2055379 / 400000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (20744641 / 12500000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (626273577 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3704899 / 1000000000) : ℝ) ≤ √(17 / (100 * 12385) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12385) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (453362879 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (5092229497 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12385) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12385) ≤ (28546903 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12385) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12385 * (161 : ℝ) ^ 2 + 26 / (10 * 12385) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12385) : ℝ)) (tA 12385 * 161 ^ 2 + 26 / (10 * 12385)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3704899 / 1000000000))) * ((2055379 / 400000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3704899 / 1000000000)) ^ 3) * ((20744641 / 12500000000000000000000))) + ((626273577 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3704899 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12385) : ℝ)) d.D d.V d.P (√(tA 12385) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3704899 / 1000000000)) ^ 2 * (((453362879 / 200000000000000)) * ((5092229497 / 125000000000000000)))) + ((626273577 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12385) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3704899 / 1000000000)) * ((2055379 / 400000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12385) : ℝ)) (tA 12385 * 161 ^ 2 + 26 / (10 * 12385)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((2055379 / 400000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3704899 / 1000000000)) ^ 2) * ((20744641 / 12500000000000000000000)) + ((626273577 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12385) : ℝ)) (√(26 / (10 * 12385) : ℝ)) d.D d.V d.P (√(tA 12385) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3704899 / 1000000000)) * (((453362879 / 200000000000000)) * ((5092229497 / 125000000000000000))) + ((626273577 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12385) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((2055379 / 400000000000000000) : ℝ) + ((626273577 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12385

namespace BstLean.Part266.Row12385
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12385 161 ∧
    0 ≤ (tableEnvelope C).f1 12385 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12385 161 ∧
    0 ≤ (tableEnvelope C).w1 12385 161 ∧ 0 ≤ (tableEnvelope C).w2 12385 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12385 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12385 161 ∧ 0 ≤ d.f1 12385 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12385 161 ∧ 0 ≤ d.w1 12385 161 ∧ 0 ≤ d.w2 12385 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12385 ≤ 2 * (228 / 100 : ℝ) / 12385 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12385 ≤ 2 * (370 / 100 : ℝ) / 12385 := by
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
    (completeRAData (tableEnvelope C) 12385 161).locationBound 12385 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12385 161).energyBound 12385 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12385 161) (d.f1 12385 161) d.f2 ≤
      32 * (((4879695713 / 1000000000000000000) : ℝ) + (162794909 / 100000000000000000) + (391278123 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12385 161) (d.w1 12385 161)
      (d.w2 12385 161) ≤
      32 * (((1976672053 / 100000000000000000000) : ℝ) + (35159109 / 2500000000000000000) + (513850817 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12385 161) (d.f1 12385 161) d.f2 ≤
      ((4879695713 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4879695713 / 1000000000000000000)) * ((162794909 / 100000000000000000)) * (126 / 100) +
      2 * (((162794909 / 100000000000000000)) ^ 2 + 2 * ((4879695713 / 1000000000000000000)) * ((391278123 / 1000000000000000000))) +
      6 * ((162794909 / 100000000000000000)) * ((391278123 / 1000000000000000000)) * (126 / 100) + 8 * ((391278123 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12385 161) (d.f1 12385 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12385 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12385 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12385 161) (d.f1 12385 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12385 161) (d.w1 12385 161) (d.w2 12385 161)
  have hwexpr0 : 0 ≤ d.w0 12385 161 + d.w1 12385 161 * √(π / 2) +
      2 * d.w2 12385 161 + energyR16 12385 *
      radiusPolynomialRoot16 (d.w0 12385 161) (d.w1 12385 161) (d.w2 12385 161) := by
    positivity
  constructor
  · change (12385 : ℝ) ^ 8 * (mA 12385 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12385 161) (d.f1 12385 161) d.f2 + locationR16 12385 *
        radiusPolynomialRoot16 (d.f0 12385 161) (d.f1 12385 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12385 : ℝ) ^ 8 * (mA 12385 : ℝ) ^ 8 *
        ((((4879695713 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4879695713 / 1000000000000000000)) * ((162794909 / 100000000000000000)) * (126 / 100) +
          2 * (((162794909 / 100000000000000000)) ^ 2 + 2 * ((4879695713 / 1000000000000000000)) * ((391278123 / 1000000000000000000))) +
          6 * ((162794909 / 100000000000000000)) * ((391278123 / 1000000000000000000)) * (126 / 100) + 8 * ((391278123 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12385) *
          (32 * (((4879695713 / 1000000000000000000) : ℝ) + (162794909 / 100000000000000000) + (391278123 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12385 : ℝ) ^ 16 *
      (d.w0 12385 161 + d.w1 12385 161 * √(π / 2) + 2 * d.w2 12385 161 +
        energyR16 12385 * radiusPolynomialRoot16 (d.w0 12385 161) (d.w1 12385 161)
          (d.w2 12385 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12385 : ℝ) ^ 16 *
        (((1976672053 / 100000000000000000000) : ℝ) + ((35159109 / 2500000000000000000)) * (126 / 100) + 2 * ((513850817 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12385) *
          (32 * (((1976672053 / 100000000000000000000) : ℝ) + (35159109 / 2500000000000000000) + (513850817 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12385

/-! A coarse bound on the actual paper statistics constant at dimension 12386. -/
namespace BstLean.Part266.Row12386
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12384 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12384 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12384 128 ≤ (12638 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12638 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12386) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12386 : ℕ))
    (by norm_num : (12386 : ℕ) ≤ 16384)
  have ht : paperTail256 12386 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12386 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12386 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12386 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12386 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12386 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12384 128 * √(2 / (12386 : ℝ)) *
      (√(12386 : ℝ) + paperT0 12386 + paperTail256 12386) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12386 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12386 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12386 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12384 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12384 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12386 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12386

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12386
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12386 (61 / 100) 161 (17 / (100 * 12386)) (26 / (10 * 12386)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12386 (61 / 100) 161 (17 / (100 * 12386)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (102744059 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (414758843 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6258651473 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12386 / 12386 * (61 / 100)) ^ 4 * inverseRadius8 (12386 - 1) /
            envelopeGap 12386 (61 / 100) 161 (17 / (100 * 12386)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12386

namespace BstLean.Part266.Row12386
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12386 161 ≤ (975741729 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12386 161 ≤ (813810003 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (391199087 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12386 161 ≤ (494048213 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12386 161 ≤ (8787647 / 625000000000000000)
  w2 : (tableEnvelope C).w2 12386 161 ≤ (256863179 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (102744059 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (102744059 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (414758843 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6258651473 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((14819 / 4000000) : ℝ) ≤ √(17 / (100 * 12386) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12386) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2266539863 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (10182814481 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12386) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12386) ≤ (14272299 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12386) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12386 * (161 : ℝ) ^ 2 + 26 / (10 * 12386) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12386) : ℝ)) (tA 12386 * 161 ^ 2 + 26 / (10 * 12386)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((14819 / 4000000))) * ((102744059 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((14819 / 4000000)) ^ 3) * ((414758843 / 250000000000000000000000))) + ((6258651473 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((14819 / 4000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12386) : ℝ)) d.D d.V d.P (√(tA 12386) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((14819 / 4000000)) ^ 2 * (((2266539863 / 1000000000000000)) * ((10182814481 / 250000000000000000)))) + ((6258651473 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12386) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((14819 / 4000000)) * ((102744059 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12386) : ℝ)) (tA 12386 * 161 ^ 2 + 26 / (10 * 12386)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((102744059 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((14819 / 4000000)) ^ 2) * ((414758843 / 250000000000000000000000)) + ((6258651473 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12386) : ℝ)) (√(26 / (10 * 12386) : ℝ)) d.D d.V d.P (√(tA 12386) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((14819 / 4000000)) * (((2266539863 / 1000000000000000)) * ((10182814481 / 250000000000000000))) + ((6258651473 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12386) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((102744059 / 20000000000000000000) : ℝ) + ((6258651473 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12386

namespace BstLean.Part266.Row12386
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12386 161 ∧
    0 ≤ (tableEnvelope C).f1 12386 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12386 161 ∧
    0 ≤ (tableEnvelope C).w1 12386 161 ∧ 0 ≤ (tableEnvelope C).w2 12386 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12386 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12386 161 ∧ 0 ≤ d.f1 12386 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12386 161 ∧ 0 ≤ d.w1 12386 161 ∧ 0 ≤ d.w2 12386 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12386 ≤ 2 * (228 / 100 : ℝ) / 12386 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12386 ≤ 2 * (370 / 100 : ℝ) / 12386 := by
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
    (completeRAData (tableEnvelope C) 12386 161).locationBound 12386 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12386 161).energyBound 12386 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12386 161) (d.f1 12386 161) d.f2 ≤
      32 * (((975741729 / 200000000000000000) : ℝ) + (813810003 / 500000000000000000) + (391199087 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12386 161) (d.w1 12386 161)
      (d.w2 12386 161) ≤
      32 * (((494048213 / 25000000000000000000) : ℝ) + (8787647 / 625000000000000000) + (256863179 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12386 161) (d.f1 12386 161) d.f2 ≤
      ((975741729 / 200000000000000000) : ℝ) ^ 2 + 2 * ((975741729 / 200000000000000000)) * ((813810003 / 500000000000000000)) * (126 / 100) +
      2 * (((813810003 / 500000000000000000)) ^ 2 + 2 * ((975741729 / 200000000000000000)) * ((391199087 / 1000000000000000000))) +
      6 * ((813810003 / 500000000000000000)) * ((391199087 / 1000000000000000000)) * (126 / 100) + 8 * ((391199087 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12386 161) (d.f1 12386 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12386 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12386 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12386 161) (d.f1 12386 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12386 161) (d.w1 12386 161) (d.w2 12386 161)
  have hwexpr0 : 0 ≤ d.w0 12386 161 + d.w1 12386 161 * √(π / 2) +
      2 * d.w2 12386 161 + energyR16 12386 *
      radiusPolynomialRoot16 (d.w0 12386 161) (d.w1 12386 161) (d.w2 12386 161) := by
    positivity
  constructor
  · change (12386 : ℝ) ^ 8 * (mA 12386 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12386 161) (d.f1 12386 161) d.f2 + locationR16 12386 *
        radiusPolynomialRoot16 (d.f0 12386 161) (d.f1 12386 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12386 : ℝ) ^ 8 * (mA 12386 : ℝ) ^ 8 *
        ((((975741729 / 200000000000000000) : ℝ) ^ 2 + 2 * ((975741729 / 200000000000000000)) * ((813810003 / 500000000000000000)) * (126 / 100) +
          2 * (((813810003 / 500000000000000000)) ^ 2 + 2 * ((975741729 / 200000000000000000)) * ((391199087 / 1000000000000000000))) +
          6 * ((813810003 / 500000000000000000)) * ((391199087 / 1000000000000000000)) * (126 / 100) + 8 * ((391199087 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12386) *
          (32 * (((975741729 / 200000000000000000) : ℝ) + (813810003 / 500000000000000000) + (391199087 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12386 : ℝ) ^ 16 *
      (d.w0 12386 161 + d.w1 12386 161 * √(π / 2) + 2 * d.w2 12386 161 +
        energyR16 12386 * radiusPolynomialRoot16 (d.w0 12386 161) (d.w1 12386 161)
          (d.w2 12386 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12386 : ℝ) ^ 16 *
        (((494048213 / 25000000000000000000) : ℝ) + ((8787647 / 625000000000000000)) * (126 / 100) + 2 * ((256863179 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12386) *
          (32 * (((494048213 / 25000000000000000000) : ℝ) + (8787647 / 625000000000000000) + (256863179 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12386

/-! A coarse bound on the actual paper statistics constant at dimension 12387. -/
namespace BstLean.Part266.Row12387
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12385 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12385 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12385 128 ≤ (12639 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12639 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12387) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12387 : ℕ))
    (by norm_num : (12387 : ℕ) ≤ 16384)
  have ht : paperTail256 12387 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12387 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12387 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12387 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12387 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12387 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12385 128 * √(2 / (12387 : ℝ)) *
      (√(12387 : ℝ) + paperT0 12387 + paperTail256 12387) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12387 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12387 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12387 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12385 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12385 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12387 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12387

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12387
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12387 (61 / 100) 161 (17 / (100 * 12387)) (26 / (10 * 12387)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12387 (61 / 100) 161 (17 / (100 * 12387)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (513595881 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1658499681 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (250182807 / 40000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12387 / 12387 * (61 / 100)) ^ 4 * inverseRadius8 (12387 - 1) /
            envelopeGap 12387 (61 / 100) 161 (17 / (100 * 12387)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12387

namespace BstLean.Part266.Row12387
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12387 161 ≤ (152428929 / 31250000000000000)
  f1 : (tableEnvelope C).f1 12387 161 ≤ (1627291911 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (391120181 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12387 161 ≤ (1975714611 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12387 161 ≤ (1405683179 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12387 161 ≤ (25680097 / 5000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (513595881 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (513595881 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1658499681 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (250182807 / 40000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((18523 / 5000000) : ℝ) ≤ √(17 / (100 * 12387) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12387) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2266265389 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40724681473 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12387) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12387) ≤ (4566767 / 40000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12387) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12387 * (161 : ℝ) ^ 2 + 26 / (10 * 12387) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12387) : ℝ)) (tA 12387 * 161 ^ 2 + 26 / (10 * 12387)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((18523 / 5000000))) * ((513595881 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((18523 / 5000000)) ^ 3) * ((1658499681 / 1000000000000000000000000))) + ((250182807 / 40000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((18523 / 5000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12387) : ℝ)) d.D d.V d.P (√(tA 12387) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((18523 / 5000000)) ^ 2 * (((2266265389 / 1000000000000000)) * ((40724681473 / 1000000000000000000)))) + ((250182807 / 40000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12387) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((18523 / 5000000)) * ((513595881 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12387) : ℝ)) (tA 12387 * 161 ^ 2 + 26 / (10 * 12387)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((513595881 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((18523 / 5000000)) ^ 2) * ((1658499681 / 1000000000000000000000000)) + ((250182807 / 40000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12387) : ℝ)) (√(26 / (10 * 12387) : ℝ)) d.D d.V d.P (√(tA 12387) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((18523 / 5000000)) * (((2266265389 / 1000000000000000)) * ((40724681473 / 1000000000000000000))) + ((250182807 / 40000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12387) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((513595881 / 100000000000000000000) : ℝ) + ((250182807 / 40000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12387

namespace BstLean.Part266.Row12387
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12387 161 ∧
    0 ≤ (tableEnvelope C).f1 12387 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12387 161 ∧
    0 ≤ (tableEnvelope C).w1 12387 161 ∧ 0 ≤ (tableEnvelope C).w2 12387 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12387 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12387 161 ∧ 0 ≤ d.f1 12387 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12387 161 ∧ 0 ≤ d.w1 12387 161 ∧ 0 ≤ d.w2 12387 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12387 ≤ 2 * (228 / 100 : ℝ) / 12387 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12387 ≤ 2 * (370 / 100 : ℝ) / 12387 := by
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
    (completeRAData (tableEnvelope C) 12387 161).locationBound 12387 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12387 161).energyBound 12387 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12387 161) (d.f1 12387 161) d.f2 ≤
      32 * (((152428929 / 31250000000000000) : ℝ) + (1627291911 / 1000000000000000000) + (391120181 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12387 161) (d.w1 12387 161)
      (d.w2 12387 161) ≤
      32 * (((1975714611 / 100000000000000000000) : ℝ) + (1405683179 / 100000000000000000000) + (25680097 / 5000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12387 161) (d.f1 12387 161) d.f2 ≤
      ((152428929 / 31250000000000000) : ℝ) ^ 2 + 2 * ((152428929 / 31250000000000000)) * ((1627291911 / 1000000000000000000)) * (126 / 100) +
      2 * (((1627291911 / 1000000000000000000)) ^ 2 + 2 * ((152428929 / 31250000000000000)) * ((391120181 / 1000000000000000000))) +
      6 * ((1627291911 / 1000000000000000000)) * ((391120181 / 1000000000000000000)) * (126 / 100) + 8 * ((391120181 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12387 161) (d.f1 12387 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12387 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12387 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12387 161) (d.f1 12387 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12387 161) (d.w1 12387 161) (d.w2 12387 161)
  have hwexpr0 : 0 ≤ d.w0 12387 161 + d.w1 12387 161 * √(π / 2) +
      2 * d.w2 12387 161 + energyR16 12387 *
      radiusPolynomialRoot16 (d.w0 12387 161) (d.w1 12387 161) (d.w2 12387 161) := by
    positivity
  constructor
  · change (12387 : ℝ) ^ 8 * (mA 12387 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12387 161) (d.f1 12387 161) d.f2 + locationR16 12387 *
        radiusPolynomialRoot16 (d.f0 12387 161) (d.f1 12387 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12387 : ℝ) ^ 8 * (mA 12387 : ℝ) ^ 8 *
        ((((152428929 / 31250000000000000) : ℝ) ^ 2 + 2 * ((152428929 / 31250000000000000)) * ((1627291911 / 1000000000000000000)) * (126 / 100) +
          2 * (((1627291911 / 1000000000000000000)) ^ 2 + 2 * ((152428929 / 31250000000000000)) * ((391120181 / 1000000000000000000))) +
          6 * ((1627291911 / 1000000000000000000)) * ((391120181 / 1000000000000000000)) * (126 / 100) + 8 * ((391120181 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12387) *
          (32 * (((152428929 / 31250000000000000) : ℝ) + (1627291911 / 1000000000000000000) + (391120181 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12387 : ℝ) ^ 16 *
      (d.w0 12387 161 + d.w1 12387 161 * √(π / 2) + 2 * d.w2 12387 161 +
        energyR16 12387 * radiusPolynomialRoot16 (d.w0 12387 161) (d.w1 12387 161)
          (d.w2 12387 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12387 : ℝ) ^ 16 *
        (((1975714611 / 100000000000000000000) : ℝ) + ((1405683179 / 100000000000000000000)) * (126 / 100) + 2 * ((25680097 / 5000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12387) *
          (32 * (((1975714611 / 100000000000000000000) : ℝ) + (1405683179 / 100000000000000000000) + (25680097 / 5000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12387

/-! A coarse bound on the actual paper statistics constant at dimension 12388. -/
namespace BstLean.Part266.Row12388
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12386 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12386 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12386 128 ≤ (12640 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12640 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12388) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12388 : ℕ))
    (by norm_num : (12388 : ℕ) ≤ 16384)
  have ht : paperTail256 12388 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12388 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12388 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12388 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12388 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12388 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12386 128 * √(2 / (12388 : ℝ)) *
      (√(12388 : ℝ) + paperT0 12388 + paperTail256 12388) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12388 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12388 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12388 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12386 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12386 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12388 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12388

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12388
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12388 (61 / 100) 161 (17 / (100 * 12388)) (26 / (10 * 12388)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12388 (61 / 100) 161 (17 / (100 * 12388)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (513471507 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (828982103 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3125245937 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12388 / 12388 * (61 / 100)) ^ 4 * inverseRadius8 (12388 - 1) /
            envelopeGap 12388 (61 / 100) 161 (17 / (100 * 12388)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12388

namespace BstLean.Part266.Row12388
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12388 161 ≤ (4876739357 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12388 161 ≤ (813481523 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (195520597 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12388 161 ≤ (1975235749 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12388 161 ≤ (1405342573 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12388 161 ≤ (256738781 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (513471507 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (513471507 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (828982103 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3125245937 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3704451 / 1000000000) : ℝ) ≤ √(17 / (100 * 12388) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12388) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2265990969 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (10179526653 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12388) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12388) ≤ (114159959 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12388) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12388 * (161 : ℝ) ^ 2 + 26 / (10 * 12388) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12388) : ℝ)) (tA 12388 * 161 ^ 2 + 26 / (10 * 12388)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3704451 / 1000000000))) * ((513471507 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3704451 / 1000000000)) ^ 3) * ((828982103 / 500000000000000000000000))) + ((3125245937 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3704451 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12388) : ℝ)) d.D d.V d.P (√(tA 12388) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3704451 / 1000000000)) ^ 2 * (((2265990969 / 1000000000000000)) * ((10179526653 / 250000000000000000)))) + ((3125245937 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12388) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3704451 / 1000000000)) * ((513471507 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12388) : ℝ)) (tA 12388 * 161 ^ 2 + 26 / (10 * 12388)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((513471507 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3704451 / 1000000000)) ^ 2) * ((828982103 / 500000000000000000000000)) + ((3125245937 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12388) : ℝ)) (√(26 / (10 * 12388) : ℝ)) d.D d.V d.P (√(tA 12388) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3704451 / 1000000000)) * (((2265990969 / 1000000000000000)) * ((10179526653 / 250000000000000000))) + ((3125245937 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12388) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((513471507 / 100000000000000000000) : ℝ) + ((3125245937 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12388

namespace BstLean.Part266.Row12388
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12388 161 ∧
    0 ≤ (tableEnvelope C).f1 12388 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12388 161 ∧
    0 ≤ (tableEnvelope C).w1 12388 161 ∧ 0 ≤ (tableEnvelope C).w2 12388 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12388 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12388 161 ∧ 0 ≤ d.f1 12388 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12388 161 ∧ 0 ≤ d.w1 12388 161 ∧ 0 ≤ d.w2 12388 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12388 ≤ 2 * (228 / 100 : ℝ) / 12388 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12388 ≤ 2 * (370 / 100 : ℝ) / 12388 := by
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
    (completeRAData (tableEnvelope C) 12388 161).locationBound 12388 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12388 161).energyBound 12388 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12388 161) (d.f1 12388 161) d.f2 ≤
      32 * (((4876739357 / 1000000000000000000) : ℝ) + (813481523 / 500000000000000000) + (195520597 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12388 161) (d.w1 12388 161)
      (d.w2 12388 161) ≤
      32 * (((1975235749 / 100000000000000000000) : ℝ) + (1405342573 / 100000000000000000000) + (256738781 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12388 161) (d.f1 12388 161) d.f2 ≤
      ((4876739357 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4876739357 / 1000000000000000000)) * ((813481523 / 500000000000000000)) * (126 / 100) +
      2 * (((813481523 / 500000000000000000)) ^ 2 + 2 * ((4876739357 / 1000000000000000000)) * ((195520597 / 500000000000000000))) +
      6 * ((813481523 / 500000000000000000)) * ((195520597 / 500000000000000000)) * (126 / 100) + 8 * ((195520597 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12388 161) (d.f1 12388 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12388 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12388 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12388 161) (d.f1 12388 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12388 161) (d.w1 12388 161) (d.w2 12388 161)
  have hwexpr0 : 0 ≤ d.w0 12388 161 + d.w1 12388 161 * √(π / 2) +
      2 * d.w2 12388 161 + energyR16 12388 *
      radiusPolynomialRoot16 (d.w0 12388 161) (d.w1 12388 161) (d.w2 12388 161) := by
    positivity
  constructor
  · change (12388 : ℝ) ^ 8 * (mA 12388 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12388 161) (d.f1 12388 161) d.f2 + locationR16 12388 *
        radiusPolynomialRoot16 (d.f0 12388 161) (d.f1 12388 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12388 : ℝ) ^ 8 * (mA 12388 : ℝ) ^ 8 *
        ((((4876739357 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4876739357 / 1000000000000000000)) * ((813481523 / 500000000000000000)) * (126 / 100) +
          2 * (((813481523 / 500000000000000000)) ^ 2 + 2 * ((4876739357 / 1000000000000000000)) * ((195520597 / 500000000000000000))) +
          6 * ((813481523 / 500000000000000000)) * ((195520597 / 500000000000000000)) * (126 / 100) + 8 * ((195520597 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12388) *
          (32 * (((4876739357 / 1000000000000000000) : ℝ) + (813481523 / 500000000000000000) + (195520597 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12388 : ℝ) ^ 16 *
      (d.w0 12388 161 + d.w1 12388 161 * √(π / 2) + 2 * d.w2 12388 161 +
        energyR16 12388 * radiusPolynomialRoot16 (d.w0 12388 161) (d.w1 12388 161)
          (d.w2 12388 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12388 : ℝ) ^ 16 *
        (((1975235749 / 100000000000000000000) : ℝ) + ((1405342573 / 100000000000000000000)) * (126 / 100) + 2 * ((256738781 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12388) *
          (32 * (((1975235749 / 100000000000000000000) : ℝ) + (1405342573 / 100000000000000000000) + (256738781 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12388

/-! A coarse bound on the actual paper statistics constant at dimension 12389. -/
namespace BstLean.Part266.Row12389
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12387 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12387 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12387 128 ≤ (12641 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12641 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12389) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12389 : ℕ))
    (by norm_num : (12389 : ℕ) ≤ 16384)
  have ht : paperTail256 12389 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12389 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12389 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12389 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12389 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12389 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12387 128 * √(2 / (12389 : ℝ)) *
      (√(12389 : ℝ) + paperT0 12389 + paperTail256 12389) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12389 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12389 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12389 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12387 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12387 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12389 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12389

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12389
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12389 (61 / 100) 161 (17 / (100 * 12389)) (26 / (10 * 12389)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12389 (61 / 100) 161 (17 / (100 * 12389)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (513347173 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1657428947 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (780802071 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12389 / 12389 * (61 / 100)) ^ 4 * inverseRadius8 (12389 - 1) /
            envelopeGap 12389 (61 / 100) 161 (17 / (100 * 12389)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12389

namespace BstLean.Part266.Row12389
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12389 161 ≤ (1218939283 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12389 161 ≤ (50832349 / 31250000000000000)
  f2 : (tableEnvelope C).f2 ≤ (390962337 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12389 161 ≤ (394951569 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12389 161 ≤ (43906327 / 3125000000000000000)
  w2 : (tableEnvelope C).w2 12389 161 ≤ (64169153 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (513347173 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (513347173 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1657428947 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (780802071 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3704301 / 1000000000) : ℝ) ≤ √(17 / (100 * 12389) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12389) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (453143321 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (20355766671 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12389) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12389) ≤ (14268843 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12389) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12389 * (161 : ℝ) ^ 2 + 26 / (10 * 12389) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12389) : ℝ)) (tA 12389 * 161 ^ 2 + 26 / (10 * 12389)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3704301 / 1000000000))) * ((513347173 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3704301 / 1000000000)) ^ 3) * ((1657428947 / 1000000000000000000000000))) + ((780802071 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3704301 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12389) : ℝ)) d.D d.V d.P (√(tA 12389) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3704301 / 1000000000)) ^ 2 * (((453143321 / 200000000000000)) * ((20355766671 / 500000000000000000)))) + ((780802071 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12389) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3704301 / 1000000000)) * ((513347173 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12389) : ℝ)) (tA 12389 * 161 ^ 2 + 26 / (10 * 12389)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((513347173 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3704301 / 1000000000)) ^ 2) * ((1657428947 / 1000000000000000000000000)) + ((780802071 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12389) : ℝ)) (√(26 / (10 * 12389) : ℝ)) d.D d.V d.P (√(tA 12389) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3704301 / 1000000000)) * (((453143321 / 200000000000000)) * ((20355766671 / 500000000000000000))) + ((780802071 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12389) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((513347173 / 100000000000000000000) : ℝ) + ((780802071 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12389

namespace BstLean.Part266.Row12389
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12389 161 ∧
    0 ≤ (tableEnvelope C).f1 12389 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12389 161 ∧
    0 ≤ (tableEnvelope C).w1 12389 161 ∧ 0 ≤ (tableEnvelope C).w2 12389 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12389 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12389 161 ∧ 0 ≤ d.f1 12389 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12389 161 ∧ 0 ≤ d.w1 12389 161 ∧ 0 ≤ d.w2 12389 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12389 ≤ 2 * (228 / 100 : ℝ) / 12389 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12389 ≤ 2 * (370 / 100 : ℝ) / 12389 := by
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
    (completeRAData (tableEnvelope C) 12389 161).locationBound 12389 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12389 161).energyBound 12389 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12389 161) (d.f1 12389 161) d.f2 ≤
      32 * (((1218939283 / 250000000000000000) : ℝ) + (50832349 / 31250000000000000) + (390962337 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12389 161) (d.w1 12389 161)
      (d.w2 12389 161) ≤
      32 * (((394951569 / 20000000000000000000) : ℝ) + (43906327 / 3125000000000000000) + (64169153 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12389 161) (d.f1 12389 161) d.f2 ≤
      ((1218939283 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1218939283 / 250000000000000000)) * ((50832349 / 31250000000000000)) * (126 / 100) +
      2 * (((50832349 / 31250000000000000)) ^ 2 + 2 * ((1218939283 / 250000000000000000)) * ((390962337 / 1000000000000000000))) +
      6 * ((50832349 / 31250000000000000)) * ((390962337 / 1000000000000000000)) * (126 / 100) + 8 * ((390962337 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12389 161) (d.f1 12389 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12389 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12389 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12389 161) (d.f1 12389 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12389 161) (d.w1 12389 161) (d.w2 12389 161)
  have hwexpr0 : 0 ≤ d.w0 12389 161 + d.w1 12389 161 * √(π / 2) +
      2 * d.w2 12389 161 + energyR16 12389 *
      radiusPolynomialRoot16 (d.w0 12389 161) (d.w1 12389 161) (d.w2 12389 161) := by
    positivity
  constructor
  · change (12389 : ℝ) ^ 8 * (mA 12389 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12389 161) (d.f1 12389 161) d.f2 + locationR16 12389 *
        radiusPolynomialRoot16 (d.f0 12389 161) (d.f1 12389 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12389 : ℝ) ^ 8 * (mA 12389 : ℝ) ^ 8 *
        ((((1218939283 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1218939283 / 250000000000000000)) * ((50832349 / 31250000000000000)) * (126 / 100) +
          2 * (((50832349 / 31250000000000000)) ^ 2 + 2 * ((1218939283 / 250000000000000000)) * ((390962337 / 1000000000000000000))) +
          6 * ((50832349 / 31250000000000000)) * ((390962337 / 1000000000000000000)) * (126 / 100) + 8 * ((390962337 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12389) *
          (32 * (((1218939283 / 250000000000000000) : ℝ) + (50832349 / 31250000000000000) + (390962337 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12389 : ℝ) ^ 16 *
      (d.w0 12389 161 + d.w1 12389 161 * √(π / 2) + 2 * d.w2 12389 161 +
        energyR16 12389 * radiusPolynomialRoot16 (d.w0 12389 161) (d.w1 12389 161)
          (d.w2 12389 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12389 : ℝ) ^ 16 *
        (((394951569 / 20000000000000000000) : ℝ) + ((43906327 / 3125000000000000000)) * (126 / 100) + 2 * ((64169153 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12389) *
          (32 * (((394951569 / 20000000000000000000) : ℝ) + (43906327 / 3125000000000000000) + (64169153 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12389

/-! A coarse bound on the actual paper statistics constant at dimension 12390. -/
namespace BstLean.Part266.Row12390
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12388 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12388 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12388 128 ≤ (12642 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12642 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12390) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12390 : ℕ))
    (by norm_num : (12390 : ℕ) ≤ 16384)
  have ht : paperTail256 12390 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12390 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12390 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12390 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12390 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12390 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12388 128 * √(2 / (12390 : ℝ)) *
      (√(12390 : ℝ) + paperT0 12390 + paperTail256 12390) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12390 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12390 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12390 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12388 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12388 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12390 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12390

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12390
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12390 (61 / 100) 161 (17 / (100 * 12390)) (26 / (10 * 12390)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12390 (61 / 100) 161 (17 / (100 * 12390)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (513222879 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (103555869 / 62500000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3121172127 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12390 / 12390 * (61 / 100)) ^ 4 * inverseRadius8 (12390 - 1) /
            envelopeGap 12390 (61 / 100) 161 (17 / (100 * 12390)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12390

namespace BstLean.Part266.Row12390
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12390 161 ≤ (974954291 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12390 161 ≤ (40657663 / 25000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (195441699 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12390 161 ≤ (49356983 / 2500000000000000000)
  w1 : (tableEnvelope C).w1 12390 161 ≤ (351165523 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12390 161 ≤ (256614463 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (513222879 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (513222879 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (103555869 / 62500000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3121172127 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((463019 / 125000000) : ℝ) ≤ √(17 / (100 * 12390) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12390) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (453088459 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (318007513 / 7812500000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12390) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12390) ≤ (114141531 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12390) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12390 * (161 : ℝ) ^ 2 + 26 / (10 * 12390) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12390) : ℝ)) (tA 12390 * 161 ^ 2 + 26 / (10 * 12390)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((463019 / 125000000))) * ((513222879 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((463019 / 125000000)) ^ 3) * ((103555869 / 62500000000000000000000))) + ((3121172127 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((463019 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12390) : ℝ)) d.D d.V d.P (√(tA 12390) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((463019 / 125000000)) ^ 2 * (((453088459 / 200000000000000)) * ((318007513 / 7812500000000000)))) + ((3121172127 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12390) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((463019 / 125000000)) * ((513222879 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12390) : ℝ)) (tA 12390 * 161 ^ 2 + 26 / (10 * 12390)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((513222879 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((463019 / 125000000)) ^ 2) * ((103555869 / 62500000000000000000000)) + ((3121172127 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12390) : ℝ)) (√(26 / (10 * 12390) : ℝ)) d.D d.V d.P (√(tA 12390) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((463019 / 125000000)) * (((453088459 / 200000000000000)) * ((318007513 / 7812500000000000))) + ((3121172127 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12390) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((513222879 / 100000000000000000000) : ℝ) + ((3121172127 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12390

namespace BstLean.Part266.Row12390
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12390 161 ∧
    0 ≤ (tableEnvelope C).f1 12390 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12390 161 ∧
    0 ≤ (tableEnvelope C).w1 12390 161 ∧ 0 ≤ (tableEnvelope C).w2 12390 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12390 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12390 161 ∧ 0 ≤ d.f1 12390 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12390 161 ∧ 0 ≤ d.w1 12390 161 ∧ 0 ≤ d.w2 12390 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12390 ≤ 2 * (228 / 100 : ℝ) / 12390 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12390 ≤ 2 * (370 / 100 : ℝ) / 12390 := by
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
    (completeRAData (tableEnvelope C) 12390 161).locationBound 12390 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12390 161).energyBound 12390 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12390 161) (d.f1 12390 161) d.f2 ≤
      32 * (((974954291 / 200000000000000000) : ℝ) + (40657663 / 25000000000000000) + (195441699 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12390 161) (d.w1 12390 161)
      (d.w2 12390 161) ≤
      32 * (((49356983 / 2500000000000000000) : ℝ) + (351165523 / 25000000000000000000) + (256614463 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12390 161) (d.f1 12390 161) d.f2 ≤
      ((974954291 / 200000000000000000) : ℝ) ^ 2 + 2 * ((974954291 / 200000000000000000)) * ((40657663 / 25000000000000000)) * (126 / 100) +
      2 * (((40657663 / 25000000000000000)) ^ 2 + 2 * ((974954291 / 200000000000000000)) * ((195441699 / 500000000000000000))) +
      6 * ((40657663 / 25000000000000000)) * ((195441699 / 500000000000000000)) * (126 / 100) + 8 * ((195441699 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12390 161) (d.f1 12390 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12390 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12390 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12390 161) (d.f1 12390 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12390 161) (d.w1 12390 161) (d.w2 12390 161)
  have hwexpr0 : 0 ≤ d.w0 12390 161 + d.w1 12390 161 * √(π / 2) +
      2 * d.w2 12390 161 + energyR16 12390 *
      radiusPolynomialRoot16 (d.w0 12390 161) (d.w1 12390 161) (d.w2 12390 161) := by
    positivity
  constructor
  · change (12390 : ℝ) ^ 8 * (mA 12390 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12390 161) (d.f1 12390 161) d.f2 + locationR16 12390 *
        radiusPolynomialRoot16 (d.f0 12390 161) (d.f1 12390 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12390 : ℝ) ^ 8 * (mA 12390 : ℝ) ^ 8 *
        ((((974954291 / 200000000000000000) : ℝ) ^ 2 + 2 * ((974954291 / 200000000000000000)) * ((40657663 / 25000000000000000)) * (126 / 100) +
          2 * (((40657663 / 25000000000000000)) ^ 2 + 2 * ((974954291 / 200000000000000000)) * ((195441699 / 500000000000000000))) +
          6 * ((40657663 / 25000000000000000)) * ((195441699 / 500000000000000000)) * (126 / 100) + 8 * ((195441699 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12390) *
          (32 * (((974954291 / 200000000000000000) : ℝ) + (40657663 / 25000000000000000) + (195441699 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12390 : ℝ) ^ 16 *
      (d.w0 12390 161 + d.w1 12390 161 * √(π / 2) + 2 * d.w2 12390 161 +
        energyR16 12390 * radiusPolynomialRoot16 (d.w0 12390 161) (d.w1 12390 161)
          (d.w2 12390 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12390 : ℝ) ^ 16 *
        (((49356983 / 2500000000000000000) : ℝ) + ((351165523 / 25000000000000000000)) * (126 / 100) + 2 * ((256614463 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12390) *
          (32 * (((49356983 / 2500000000000000000) : ℝ) + (351165523 / 25000000000000000000) + (256614463 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12390

/-! A coarse bound on the actual paper statistics constant at dimension 12391. -/
namespace BstLean.Part266.Row12391
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12389 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12389 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12389 128 ≤ (12643 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12643 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12391) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12391 : ℕ))
    (by norm_num : (12391 : ℕ) ≤ 16384)
  have ht : paperTail256 12391 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12391 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12391 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12391 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12391 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12391 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12389 128 * √(2 / (12391 : ℝ)) *
      (√(12391 : ℝ) + paperT0 12391 + paperTail256 12391) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12391 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12391 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12391 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12389 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12389 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12391 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12391

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12391
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12391 (61 / 100) 161 (17 / (100 * 12391)) (26 / (10 * 12391)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12391 (61 / 100) 161 (17 / (100 * 12391)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (4104789 / 800000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1656359077 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (623827493 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12391 / 12391 * (61 / 100)) ^ 4 * inverseRadius8 (12391 - 1) /
            envelopeGap 12391 (61 / 100) 161 (17 / (100 * 12391)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12391

namespace BstLean.Part266.Row12391
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12391 161 ≤ (1218447481 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12391 161 ≤ (812989429 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (97701147 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12391 161 ≤ (1973801753 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12391 161 ≤ (175540277 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 12391 161 ≤ (128276167 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (4104789 / 800000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (4104789 / 800000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1656359077 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (623827493 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1852001 / 500000000) : ℝ) ≤ √(17 / (100 * 12391) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12391) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2265168041 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (20349195789 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12391) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12391) ≤ (114132319 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12391) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12391 * (161 : ℝ) ^ 2 + 26 / (10 * 12391) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12391) : ℝ)) (tA 12391 * 161 ^ 2 + 26 / (10 * 12391)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1852001 / 500000000))) * ((4104789 / 800000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1852001 / 500000000)) ^ 3) * ((1656359077 / 1000000000000000000000000))) + ((623827493 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1852001 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12391) : ℝ)) d.D d.V d.P (√(tA 12391) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1852001 / 500000000)) ^ 2 * (((2265168041 / 1000000000000000)) * ((20349195789 / 500000000000000000)))) + ((623827493 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12391) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1852001 / 500000000)) * ((4104789 / 800000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12391) : ℝ)) (tA 12391 * 161 ^ 2 + 26 / (10 * 12391)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((4104789 / 800000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1852001 / 500000000)) ^ 2) * ((1656359077 / 1000000000000000000000000)) + ((623827493 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12391) : ℝ)) (√(26 / (10 * 12391) : ℝ)) d.D d.V d.P (√(tA 12391) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1852001 / 500000000)) * (((2265168041 / 1000000000000000)) * ((20349195789 / 500000000000000000))) + ((623827493 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12391) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((4104789 / 800000000000000000) : ℝ) + ((623827493 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12391

namespace BstLean.Part266.Row12391
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12391 161 ∧
    0 ≤ (tableEnvelope C).f1 12391 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12391 161 ∧
    0 ≤ (tableEnvelope C).w1 12391 161 ∧ 0 ≤ (tableEnvelope C).w2 12391 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12391 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12391 161 ∧ 0 ≤ d.f1 12391 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12391 161 ∧ 0 ≤ d.w1 12391 161 ∧ 0 ≤ d.w2 12391 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12391 ≤ 2 * (228 / 100 : ℝ) / 12391 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12391 ≤ 2 * (370 / 100 : ℝ) / 12391 := by
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
    (completeRAData (tableEnvelope C) 12391 161).locationBound 12391 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12391 161).energyBound 12391 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12391 161) (d.f1 12391 161) d.f2 ≤
      32 * (((1218447481 / 250000000000000000) : ℝ) + (812989429 / 500000000000000000) + (97701147 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12391 161) (d.w1 12391 161)
      (d.w2 12391 161) ≤
      32 * (((1973801753 / 100000000000000000000) : ℝ) + (175540277 / 12500000000000000000) + (128276167 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12391 161) (d.f1 12391 161) d.f2 ≤
      ((1218447481 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1218447481 / 250000000000000000)) * ((812989429 / 500000000000000000)) * (126 / 100) +
      2 * (((812989429 / 500000000000000000)) ^ 2 + 2 * ((1218447481 / 250000000000000000)) * ((97701147 / 250000000000000000))) +
      6 * ((812989429 / 500000000000000000)) * ((97701147 / 250000000000000000)) * (126 / 100) + 8 * ((97701147 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12391 161) (d.f1 12391 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12391 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12391 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12391 161) (d.f1 12391 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12391 161) (d.w1 12391 161) (d.w2 12391 161)
  have hwexpr0 : 0 ≤ d.w0 12391 161 + d.w1 12391 161 * √(π / 2) +
      2 * d.w2 12391 161 + energyR16 12391 *
      radiusPolynomialRoot16 (d.w0 12391 161) (d.w1 12391 161) (d.w2 12391 161) := by
    positivity
  constructor
  · change (12391 : ℝ) ^ 8 * (mA 12391 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12391 161) (d.f1 12391 161) d.f2 + locationR16 12391 *
        radiusPolynomialRoot16 (d.f0 12391 161) (d.f1 12391 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12391 : ℝ) ^ 8 * (mA 12391 : ℝ) ^ 8 *
        ((((1218447481 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1218447481 / 250000000000000000)) * ((812989429 / 500000000000000000)) * (126 / 100) +
          2 * (((812989429 / 500000000000000000)) ^ 2 + 2 * ((1218447481 / 250000000000000000)) * ((97701147 / 250000000000000000))) +
          6 * ((812989429 / 500000000000000000)) * ((97701147 / 250000000000000000)) * (126 / 100) + 8 * ((97701147 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12391) *
          (32 * (((1218447481 / 250000000000000000) : ℝ) + (812989429 / 500000000000000000) + (97701147 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12391 : ℝ) ^ 16 *
      (d.w0 12391 161 + d.w1 12391 161 * √(π / 2) + 2 * d.w2 12391 161 +
        energyR16 12391 * radiusPolynomialRoot16 (d.w0 12391 161) (d.w1 12391 161)
          (d.w2 12391 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12391 : ℝ) ^ 16 *
        (((1973801753 / 100000000000000000000) : ℝ) + ((175540277 / 12500000000000000000)) * (126 / 100) + 2 * ((128276167 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12391) *
          (32 * (((1973801753 / 100000000000000000000) : ℝ) + (175540277 / 12500000000000000000) + (128276167 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12391

/-! A coarse bound on the actual paper statistics constant at dimension 12392. -/
namespace BstLean.Part266.Row12392
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12390 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12390 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12390 128 ≤ (12644 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12644 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12392) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12392 : ℕ))
    (by norm_num : (12392 : ℕ) ≤ 16384)
  have ht : paperTail256 12392 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12392 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12392 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12392 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12392 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12392 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12390 128 * √(2 / (12392 : ℝ)) *
      (√(12392 : ℝ) + paperT0 12392 + paperTail256 12392) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12392 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12392 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12392 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12390 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12390 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12392 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12392

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12392
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12392 (61 / 100) 161 (17 / (100 * 12392)) (26 / (10 * 12392)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12392 (61 / 100) 161 (17 / (100 * 12392)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (128243603 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (827912233 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6234208593 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12392 / 12392 * (61 / 100)) ^ 4 * inverseRadius8 (12392 - 1) /
            envelopeGap 12392 (61 / 100) 161 (17 / (100 * 12392)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12392

namespace BstLean.Part266.Row12392
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12392 161 ≤ (2436402471 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12392 161 ≤ (406412607 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (195362849 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12392 161 ≤ (1973323567 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12392 161 ≤ (701991039 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12392 161 ≤ (128245113 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (128243603 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (128243603 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (827912233 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6234208593 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3703853 / 1000000000) : ℝ) ≤ √(17 / (100 * 12392) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12392) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2264893843 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (20345911543 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12392) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12392) ≤ (114123109 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12392) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12392 * (161 : ℝ) ^ 2 + 26 / (10 * 12392) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12392) : ℝ)) (tA 12392 * 161 ^ 2 + 26 / (10 * 12392)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3703853 / 1000000000))) * ((128243603 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3703853 / 1000000000)) ^ 3) * ((827912233 / 500000000000000000000000))) + ((6234208593 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3703853 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12392) : ℝ)) d.D d.V d.P (√(tA 12392) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3703853 / 1000000000)) ^ 2 * (((2264893843 / 1000000000000000)) * ((20345911543 / 500000000000000000)))) + ((6234208593 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12392) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3703853 / 1000000000)) * ((128243603 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12392) : ℝ)) (tA 12392 * 161 ^ 2 + 26 / (10 * 12392)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((128243603 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3703853 / 1000000000)) ^ 2) * ((827912233 / 500000000000000000000000)) + ((6234208593 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12392) : ℝ)) (√(26 / (10 * 12392) : ℝ)) d.D d.V d.P (√(tA 12392) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3703853 / 1000000000)) * (((2264893843 / 1000000000000000)) * ((20345911543 / 500000000000000000))) + ((6234208593 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12392) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((128243603 / 25000000000000000000) : ℝ) + ((6234208593 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12392

namespace BstLean.Part266.Row12392
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12392 161 ∧
    0 ≤ (tableEnvelope C).f1 12392 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12392 161 ∧
    0 ≤ (tableEnvelope C).w1 12392 161 ∧ 0 ≤ (tableEnvelope C).w2 12392 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12392 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12392 161 ∧ 0 ≤ d.f1 12392 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12392 161 ∧ 0 ≤ d.w1 12392 161 ∧ 0 ≤ d.w2 12392 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12392 ≤ 2 * (228 / 100 : ℝ) / 12392 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12392 ≤ 2 * (370 / 100 : ℝ) / 12392 := by
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
    (completeRAData (tableEnvelope C) 12392 161).locationBound 12392 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12392 161).energyBound 12392 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12392 161) (d.f1 12392 161) d.f2 ≤
      32 * (((2436402471 / 500000000000000000) : ℝ) + (406412607 / 250000000000000000) + (195362849 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12392 161) (d.w1 12392 161)
      (d.w2 12392 161) ≤
      32 * (((1973323567 / 100000000000000000000) : ℝ) + (701991039 / 50000000000000000000) + (128245113 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12392 161) (d.f1 12392 161) d.f2 ≤
      ((2436402471 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2436402471 / 500000000000000000)) * ((406412607 / 250000000000000000)) * (126 / 100) +
      2 * (((406412607 / 250000000000000000)) ^ 2 + 2 * ((2436402471 / 500000000000000000)) * ((195362849 / 500000000000000000))) +
      6 * ((406412607 / 250000000000000000)) * ((195362849 / 500000000000000000)) * (126 / 100) + 8 * ((195362849 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12392 161) (d.f1 12392 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12392 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12392 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12392 161) (d.f1 12392 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12392 161) (d.w1 12392 161) (d.w2 12392 161)
  have hwexpr0 : 0 ≤ d.w0 12392 161 + d.w1 12392 161 * √(π / 2) +
      2 * d.w2 12392 161 + energyR16 12392 *
      radiusPolynomialRoot16 (d.w0 12392 161) (d.w1 12392 161) (d.w2 12392 161) := by
    positivity
  constructor
  · change (12392 : ℝ) ^ 8 * (mA 12392 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12392 161) (d.f1 12392 161) d.f2 + locationR16 12392 *
        radiusPolynomialRoot16 (d.f0 12392 161) (d.f1 12392 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12392 : ℝ) ^ 8 * (mA 12392 : ℝ) ^ 8 *
        ((((2436402471 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2436402471 / 500000000000000000)) * ((406412607 / 250000000000000000)) * (126 / 100) +
          2 * (((406412607 / 250000000000000000)) ^ 2 + 2 * ((2436402471 / 500000000000000000)) * ((195362849 / 500000000000000000))) +
          6 * ((406412607 / 250000000000000000)) * ((195362849 / 500000000000000000)) * (126 / 100) + 8 * ((195362849 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12392) *
          (32 * (((2436402471 / 500000000000000000) : ℝ) + (406412607 / 250000000000000000) + (195362849 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12392 : ℝ) ^ 16 *
      (d.w0 12392 161 + d.w1 12392 161 * √(π / 2) + 2 * d.w2 12392 161 +
        energyR16 12392 * radiusPolynomialRoot16 (d.w0 12392 161) (d.w1 12392 161)
          (d.w2 12392 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12392 : ℝ) ^ 16 *
        (((1973323567 / 100000000000000000000) : ℝ) + ((701991039 / 50000000000000000000)) * (126 / 100) + 2 * ((128245113 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12392) *
          (32 * (((1973323567 / 100000000000000000000) : ℝ) + (701991039 / 50000000000000000000) + (128245113 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12392

/-! A coarse bound on the actual paper statistics constant at dimension 12393. -/
namespace BstLean.Part266.Row12393
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12391 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12391 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12391 128 ≤ (12645 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12645 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12393) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12393 : ℕ))
    (by norm_num : (12393 : ℕ) ≤ 16384)
  have ht : paperTail256 12393 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12393 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12393 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12393 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12393 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12393 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12391 128 * √(2 / (12393 : ℝ)) *
      (√(12393 : ℝ) + paperT0 12393 + paperTail256 12393) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12393 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12393 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12393 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12391 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12391 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12393 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12393

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12393
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12393 (61 / 100) 161 (17 / (100 * 12393)) (26 / (10 * 12393)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12393 (61 / 100) 161 (17 / (100 * 12393)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (256425119 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1655290071 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6230145241 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12393 / 12393 * (61 / 100)) ^ 4 * inverseRadius8 (12393 - 1) /
            envelopeGap 12393 (61 / 100) 161 (17 / (100 * 12393)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12393

namespace BstLean.Part266.Row12393
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12393 161 ≤ (608978013 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12393 161 ≤ (203165373 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (390646937 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12393 161 ≤ (1972846337 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12393 161 ≤ (280728487 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12393 161 ≤ (256428137 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (256425119 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (256425119 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1655290071 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6230145241 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3703703 / 1000000000) : ℝ) ≤ √(17 / (100 * 12393) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12393) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2264619699 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40685256187 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12393) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12393) ≤ (1141139 / 10000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12393) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12393 * (161 : ℝ) ^ 2 + 26 / (10 * 12393) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12393) : ℝ)) (tA 12393 * 161 ^ 2 + 26 / (10 * 12393)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3703703 / 1000000000))) * ((256425119 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3703703 / 1000000000)) ^ 3) * ((1655290071 / 1000000000000000000000000))) + ((6230145241 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3703703 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12393) : ℝ)) d.D d.V d.P (√(tA 12393) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3703703 / 1000000000)) ^ 2 * (((2264619699 / 1000000000000000)) * ((40685256187 / 1000000000000000000)))) + ((6230145241 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12393) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3703703 / 1000000000)) * ((256425119 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12393) : ℝ)) (tA 12393 * 161 ^ 2 + 26 / (10 * 12393)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((256425119 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3703703 / 1000000000)) ^ 2) * ((1655290071 / 1000000000000000000000000)) + ((6230145241 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12393) : ℝ)) (√(26 / (10 * 12393) : ℝ)) d.D d.V d.P (√(tA 12393) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3703703 / 1000000000)) * (((2264619699 / 1000000000000000)) * ((40685256187 / 1000000000000000000))) + ((6230145241 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12393) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((256425119 / 50000000000000000000) : ℝ) + ((6230145241 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12393

namespace BstLean.Part266.Row12393
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12393 161 ∧
    0 ≤ (tableEnvelope C).f1 12393 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12393 161 ∧
    0 ≤ (tableEnvelope C).w1 12393 161 ∧ 0 ≤ (tableEnvelope C).w2 12393 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12393 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12393 161 ∧ 0 ≤ d.f1 12393 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12393 161 ∧ 0 ≤ d.w1 12393 161 ∧ 0 ≤ d.w2 12393 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12393 ≤ 2 * (228 / 100 : ℝ) / 12393 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12393 ≤ 2 * (370 / 100 : ℝ) / 12393 := by
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
    (completeRAData (tableEnvelope C) 12393 161).locationBound 12393 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12393 161).energyBound 12393 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12393 161) (d.f1 12393 161) d.f2 ≤
      32 * (((608978013 / 125000000000000000) : ℝ) + (203165373 / 125000000000000000) + (390646937 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12393 161) (d.w1 12393 161)
      (d.w2 12393 161) ≤
      32 * (((1972846337 / 100000000000000000000) : ℝ) + (280728487 / 20000000000000000000) + (256428137 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12393 161) (d.f1 12393 161) d.f2 ≤
      ((608978013 / 125000000000000000) : ℝ) ^ 2 + 2 * ((608978013 / 125000000000000000)) * ((203165373 / 125000000000000000)) * (126 / 100) +
      2 * (((203165373 / 125000000000000000)) ^ 2 + 2 * ((608978013 / 125000000000000000)) * ((390646937 / 1000000000000000000))) +
      6 * ((203165373 / 125000000000000000)) * ((390646937 / 1000000000000000000)) * (126 / 100) + 8 * ((390646937 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12393 161) (d.f1 12393 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12393 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12393 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12393 161) (d.f1 12393 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12393 161) (d.w1 12393 161) (d.w2 12393 161)
  have hwexpr0 : 0 ≤ d.w0 12393 161 + d.w1 12393 161 * √(π / 2) +
      2 * d.w2 12393 161 + energyR16 12393 *
      radiusPolynomialRoot16 (d.w0 12393 161) (d.w1 12393 161) (d.w2 12393 161) := by
    positivity
  constructor
  · change (12393 : ℝ) ^ 8 * (mA 12393 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12393 161) (d.f1 12393 161) d.f2 + locationR16 12393 *
        radiusPolynomialRoot16 (d.f0 12393 161) (d.f1 12393 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12393 : ℝ) ^ 8 * (mA 12393 : ℝ) ^ 8 *
        ((((608978013 / 125000000000000000) : ℝ) ^ 2 + 2 * ((608978013 / 125000000000000000)) * ((203165373 / 125000000000000000)) * (126 / 100) +
          2 * (((203165373 / 125000000000000000)) ^ 2 + 2 * ((608978013 / 125000000000000000)) * ((390646937 / 1000000000000000000))) +
          6 * ((203165373 / 125000000000000000)) * ((390646937 / 1000000000000000000)) * (126 / 100) + 8 * ((390646937 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12393) *
          (32 * (((608978013 / 125000000000000000) : ℝ) + (203165373 / 125000000000000000) + (390646937 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12393 : ℝ) ^ 16 *
      (d.w0 12393 161 + d.w1 12393 161 * √(π / 2) + 2 * d.w2 12393 161 +
        energyR16 12393 * radiusPolynomialRoot16 (d.w0 12393 161) (d.w1 12393 161)
          (d.w2 12393 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12393 : ℝ) ^ 16 *
        (((1972846337 / 100000000000000000000) : ℝ) + ((280728487 / 20000000000000000000)) * (126 / 100) + 2 * ((256428137 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12393) *
          (32 * (((1972846337 / 100000000000000000000) : ℝ) + (280728487 / 20000000000000000000) + (256428137 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12393

/-! A coarse bound on the actual paper statistics constant at dimension 12394. -/
namespace BstLean.Part266.Row12394
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12392 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12392 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12392 128 ≤ (12646 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12646 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12394) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12394 : ℕ))
    (by norm_num : (12394 : ℕ) ≤ 16384)
  have ht : paperTail256 12394 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12394 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12394 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12394 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12394 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12394 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12392 128 * √(2 / (12394 : ℝ)) *
      (√(12394 : ℝ) + paperT0 12394 + paperTail256 12394) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12394 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12394 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12394 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12392 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12392 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12394 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12394

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12394
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12394 (61 / 100) 161 (17 / (100 * 12394)) (26 / (10 * 12394)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12394 (61 / 100) 161 (17 / (100 * 12394)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (102545221 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1654755891 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6226084871 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12394 / 12394 * (61 / 100)) ^ 4 * inverseRadius8 (12394 - 1) /
            envelopeGap 12394 (61 / 100) 161 (17 / (100 * 12394)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12394

namespace BstLean.Part266.Row12394
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12394 161 ≤ (2435419907 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12394 161 ≤ (1624994771 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (12205253 / 31250000000000000)
  w0 : (tableEnvelope C).w0 12394 161 ≤ (1972368487 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12394 161 ≤ (1403302531 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12394 161 ≤ (512732137 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (102545221 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (102545221 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1654755891 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6226084871 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1851777 / 500000000) : ℝ) ≤ √(17 / (100 * 12394) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12394) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (566086403 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (5084836359 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12394) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12394) ≤ (114104693 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12394) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12394 * (161 : ℝ) ^ 2 + 26 / (10 * 12394) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12394) : ℝ)) (tA 12394 * 161 ^ 2 + 26 / (10 * 12394)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1851777 / 500000000))) * ((102545221 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1851777 / 500000000)) ^ 3) * ((1654755891 / 1000000000000000000000000))) + ((6226084871 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1851777 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12394) : ℝ)) d.D d.V d.P (√(tA 12394) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1851777 / 500000000)) ^ 2 * (((566086403 / 250000000000000)) * ((5084836359 / 125000000000000000)))) + ((6226084871 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12394) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1851777 / 500000000)) * ((102545221 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12394) : ℝ)) (tA 12394 * 161 ^ 2 + 26 / (10 * 12394)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((102545221 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1851777 / 500000000)) ^ 2) * ((1654755891 / 1000000000000000000000000)) + ((6226084871 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12394) : ℝ)) (√(26 / (10 * 12394) : ℝ)) d.D d.V d.P (√(tA 12394) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1851777 / 500000000)) * (((566086403 / 250000000000000)) * ((5084836359 / 125000000000000000))) + ((6226084871 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12394) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((102545221 / 20000000000000000000) : ℝ) + ((6226084871 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12394

namespace BstLean.Part266.Row12394
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12394 161 ∧
    0 ≤ (tableEnvelope C).f1 12394 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12394 161 ∧
    0 ≤ (tableEnvelope C).w1 12394 161 ∧ 0 ≤ (tableEnvelope C).w2 12394 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12394 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12394 161 ∧ 0 ≤ d.f1 12394 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12394 161 ∧ 0 ≤ d.w1 12394 161 ∧ 0 ≤ d.w2 12394 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12394 ≤ 2 * (228 / 100 : ℝ) / 12394 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12394 ≤ 2 * (370 / 100 : ℝ) / 12394 := by
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
    (completeRAData (tableEnvelope C) 12394 161).locationBound 12394 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12394 161).energyBound 12394 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12394 161) (d.f1 12394 161) d.f2 ≤
      32 * (((2435419907 / 500000000000000000) : ℝ) + (1624994771 / 1000000000000000000) + (12205253 / 31250000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12394 161) (d.w1 12394 161)
      (d.w2 12394 161) ≤
      32 * (((1972368487 / 100000000000000000000) : ℝ) + (1403302531 / 100000000000000000000) + (512732137 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12394 161) (d.f1 12394 161) d.f2 ≤
      ((2435419907 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2435419907 / 500000000000000000)) * ((1624994771 / 1000000000000000000)) * (126 / 100) +
      2 * (((1624994771 / 1000000000000000000)) ^ 2 + 2 * ((2435419907 / 500000000000000000)) * ((12205253 / 31250000000000000))) +
      6 * ((1624994771 / 1000000000000000000)) * ((12205253 / 31250000000000000)) * (126 / 100) + 8 * ((12205253 / 31250000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12394 161) (d.f1 12394 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12394 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12394 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12394 161) (d.f1 12394 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12394 161) (d.w1 12394 161) (d.w2 12394 161)
  have hwexpr0 : 0 ≤ d.w0 12394 161 + d.w1 12394 161 * √(π / 2) +
      2 * d.w2 12394 161 + energyR16 12394 *
      radiusPolynomialRoot16 (d.w0 12394 161) (d.w1 12394 161) (d.w2 12394 161) := by
    positivity
  constructor
  · change (12394 : ℝ) ^ 8 * (mA 12394 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12394 161) (d.f1 12394 161) d.f2 + locationR16 12394 *
        radiusPolynomialRoot16 (d.f0 12394 161) (d.f1 12394 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12394 : ℝ) ^ 8 * (mA 12394 : ℝ) ^ 8 *
        ((((2435419907 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2435419907 / 500000000000000000)) * ((1624994771 / 1000000000000000000)) * (126 / 100) +
          2 * (((1624994771 / 1000000000000000000)) ^ 2 + 2 * ((2435419907 / 500000000000000000)) * ((12205253 / 31250000000000000))) +
          6 * ((1624994771 / 1000000000000000000)) * ((12205253 / 31250000000000000)) * (126 / 100) + 8 * ((12205253 / 31250000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12394) *
          (32 * (((2435419907 / 500000000000000000) : ℝ) + (1624994771 / 1000000000000000000) + (12205253 / 31250000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12394 : ℝ) ^ 16 *
      (d.w0 12394 161 + d.w1 12394 161 * √(π / 2) + 2 * d.w2 12394 161 +
        energyR16 12394 * radiusPolynomialRoot16 (d.w0 12394 161) (d.w1 12394 161)
          (d.w2 12394 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12394 : ℝ) ^ 16 *
        (((1972368487 / 100000000000000000000) : ℝ) + ((1403302531 / 100000000000000000000)) * (126 / 100) + 2 * ((512732137 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12394) *
          (32 * (((1972368487 / 100000000000000000000) : ℝ) + (1403302531 / 100000000000000000000) + (512732137 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12394

/-! A coarse bound on the actual paper statistics constant at dimension 12395. -/
namespace BstLean.Part266.Row12395
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12393 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12393 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12393 128 ≤ (12647 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12647 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12395) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12395 : ℕ))
    (by norm_num : (12395 : ℕ) ≤ 16384)
  have ht : paperTail256 12395 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12395 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12395 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12395 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12395 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12395 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12393 128 * √(2 / (12395 : ℝ)) *
      (√(12395 : ℝ) + paperT0 12395 + paperTail256 12395) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12395 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12395 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12395 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12393 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12393 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12395 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12395

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12395
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12395 (61 / 100) 161 (17 / (100 * 12395)) (26 / (10 * 12395)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12395 (61 / 100) 161 (17 / (100 * 12395)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (128150503 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (827110963 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3111013741 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12395 / 12395 * (61 / 100)) ^ 4 * inverseRadius8 (12395 - 1) /
            envelopeGap 12395 (61 / 100) 161 (17 / (100 * 12395)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12395

namespace BstLean.Part266.Row12395
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12395 161 ≤ (973971933 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12395 161 ≤ (203083443 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (390489383 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12395 161 ≤ (985945797 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12395 161 ≤ (701481561 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12395 161 ≤ (12815201 / 2500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (128150503 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (128150503 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (827110963 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3111013741 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((925851 / 250000000) : ℝ) ≤ √(17 / (100 * 12395) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12395) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2264071581 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40672127139 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12395) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12395) ≤ (891371 / 7812500000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12395) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12395 * (161 : ℝ) ^ 2 + 26 / (10 * 12395) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12395) : ℝ)) (tA 12395 * 161 ^ 2 + 26 / (10 * 12395)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((925851 / 250000000))) * ((128150503 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((925851 / 250000000)) ^ 3) * ((827110963 / 500000000000000000000000))) + ((3111013741 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((925851 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12395) : ℝ)) d.D d.V d.P (√(tA 12395) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((925851 / 250000000)) ^ 2 * (((2264071581 / 1000000000000000)) * ((40672127139 / 1000000000000000000)))) + ((3111013741 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12395) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((925851 / 250000000)) * ((128150503 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12395) : ℝ)) (tA 12395 * 161 ^ 2 + 26 / (10 * 12395)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((128150503 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((925851 / 250000000)) ^ 2) * ((827110963 / 500000000000000000000000)) + ((3111013741 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12395) : ℝ)) (√(26 / (10 * 12395) : ℝ)) d.D d.V d.P (√(tA 12395) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((925851 / 250000000)) * (((2264071581 / 1000000000000000)) * ((40672127139 / 1000000000000000000))) + ((3111013741 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12395) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((128150503 / 25000000000000000000) : ℝ) + ((3111013741 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12395

namespace BstLean.Part266.Row12395
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12395 161 ∧
    0 ≤ (tableEnvelope C).f1 12395 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12395 161 ∧
    0 ≤ (tableEnvelope C).w1 12395 161 ∧ 0 ≤ (tableEnvelope C).w2 12395 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12395 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12395 161 ∧ 0 ≤ d.f1 12395 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12395 161 ∧ 0 ≤ d.w1 12395 161 ∧ 0 ≤ d.w2 12395 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12395 ≤ 2 * (228 / 100 : ℝ) / 12395 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12395 ≤ 2 * (370 / 100 : ℝ) / 12395 := by
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
    (completeRAData (tableEnvelope C) 12395 161).locationBound 12395 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12395 161).energyBound 12395 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12395 161) (d.f1 12395 161) d.f2 ≤
      32 * (((973971933 / 200000000000000000) : ℝ) + (203083443 / 125000000000000000) + (390489383 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12395 161) (d.w1 12395 161)
      (d.w2 12395 161) ≤
      32 * (((985945797 / 50000000000000000000) : ℝ) + (701481561 / 50000000000000000000) + (12815201 / 2500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12395 161) (d.f1 12395 161) d.f2 ≤
      ((973971933 / 200000000000000000) : ℝ) ^ 2 + 2 * ((973971933 / 200000000000000000)) * ((203083443 / 125000000000000000)) * (126 / 100) +
      2 * (((203083443 / 125000000000000000)) ^ 2 + 2 * ((973971933 / 200000000000000000)) * ((390489383 / 1000000000000000000))) +
      6 * ((203083443 / 125000000000000000)) * ((390489383 / 1000000000000000000)) * (126 / 100) + 8 * ((390489383 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12395 161) (d.f1 12395 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12395 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12395 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12395 161) (d.f1 12395 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12395 161) (d.w1 12395 161) (d.w2 12395 161)
  have hwexpr0 : 0 ≤ d.w0 12395 161 + d.w1 12395 161 * √(π / 2) +
      2 * d.w2 12395 161 + energyR16 12395 *
      radiusPolynomialRoot16 (d.w0 12395 161) (d.w1 12395 161) (d.w2 12395 161) := by
    positivity
  constructor
  · change (12395 : ℝ) ^ 8 * (mA 12395 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12395 161) (d.f1 12395 161) d.f2 + locationR16 12395 *
        radiusPolynomialRoot16 (d.f0 12395 161) (d.f1 12395 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12395 : ℝ) ^ 8 * (mA 12395 : ℝ) ^ 8 *
        ((((973971933 / 200000000000000000) : ℝ) ^ 2 + 2 * ((973971933 / 200000000000000000)) * ((203083443 / 125000000000000000)) * (126 / 100) +
          2 * (((203083443 / 125000000000000000)) ^ 2 + 2 * ((973971933 / 200000000000000000)) * ((390489383 / 1000000000000000000))) +
          6 * ((203083443 / 125000000000000000)) * ((390489383 / 1000000000000000000)) * (126 / 100) + 8 * ((390489383 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12395) *
          (32 * (((973971933 / 200000000000000000) : ℝ) + (203083443 / 125000000000000000) + (390489383 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12395 : ℝ) ^ 16 *
      (d.w0 12395 161 + d.w1 12395 161 * √(π / 2) + 2 * d.w2 12395 161 +
        energyR16 12395 * radiusPolynomialRoot16 (d.w0 12395 161) (d.w1 12395 161)
          (d.w2 12395 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12395 : ℝ) ^ 16 *
        (((985945797 / 50000000000000000000) : ℝ) + ((701481561 / 50000000000000000000)) * (126 / 100) + 2 * ((12815201 / 2500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12395) *
          (32 * (((985945797 / 50000000000000000000) : ℝ) + (701481561 / 50000000000000000000) + (12815201 / 2500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12395

/-! A coarse bound on the actual paper statistics constant at dimension 12396. -/
namespace BstLean.Part266.Row12396
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12394 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12394 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12394 128 ≤ (12648 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12648 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12396) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12396 : ℕ))
    (by norm_num : (12396 : ℕ) ≤ 16384)
  have ht : paperTail256 12396 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12396 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12396 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12396 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12396 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12396 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12394 128 * √(2 / (12396 : ℝ)) *
      (√(12396 : ℝ) + paperT0 12396 + paperTail256 12396) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12396 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12396 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12396 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12394 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12394 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12396 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12396

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12396
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12396 (61 / 100) 161 (17 / (100 * 12396)) (26 / (10 * 12396)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12396 (61 / 100) 161 (17 / (100 * 12396)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (256238979 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1653688177 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (621797307 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12396 / 12396 * (61 / 100)) ^ 4 * inverseRadius8 (12396 - 1) /
            envelopeGap 12396 (61 / 100) 161 (17 / (100 * 12396)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12396

namespace BstLean.Part266.Row12396
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12396 161 ≤ (1217219017 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12396 161 ≤ (1624339547 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (390410589 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12396 161 ≤ (6160669 / 312500000000000000)
  w1 : (tableEnvelope C).w1 12396 161 ≤ (1402623449 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12396 161 ≤ (256241991 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (256238979 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (256238979 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1653688177 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (621797307 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((740651 / 200000000) : ℝ) ≤ √(17 / (100 * 12396) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12396) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1131898801 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40665565003 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12396) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12396) ≤ (114086283 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12396) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12396 * (161 : ℝ) ^ 2 + 26 / (10 * 12396) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12396) : ℝ)) (tA 12396 * 161 ^ 2 + 26 / (10 * 12396)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((740651 / 200000000))) * ((256238979 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((740651 / 200000000)) ^ 3) * ((1653688177 / 1000000000000000000000000))) + ((621797307 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((740651 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12396) : ℝ)) d.D d.V d.P (√(tA 12396) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((740651 / 200000000)) ^ 2 * (((1131898801 / 500000000000000)) * ((40665565003 / 1000000000000000000)))) + ((621797307 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12396) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((740651 / 200000000)) * ((256238979 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12396) : ℝ)) (tA 12396 * 161 ^ 2 + 26 / (10 * 12396)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((256238979 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((740651 / 200000000)) ^ 2) * ((1653688177 / 1000000000000000000000000)) + ((621797307 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12396) : ℝ)) (√(26 / (10 * 12396) : ℝ)) d.D d.V d.P (√(tA 12396) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((740651 / 200000000)) * (((1131898801 / 500000000000000)) * ((40665565003 / 1000000000000000000))) + ((621797307 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12396) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((256238979 / 50000000000000000000) : ℝ) + ((621797307 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12396

namespace BstLean.Part266.Row12396
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12396 161 ∧
    0 ≤ (tableEnvelope C).f1 12396 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12396 161 ∧
    0 ≤ (tableEnvelope C).w1 12396 161 ∧ 0 ≤ (tableEnvelope C).w2 12396 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12396 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12396 161 ∧ 0 ≤ d.f1 12396 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12396 161 ∧ 0 ≤ d.w1 12396 161 ∧ 0 ≤ d.w2 12396 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12396 ≤ 2 * (228 / 100 : ℝ) / 12396 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12396 ≤ 2 * (370 / 100 : ℝ) / 12396 := by
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
    (completeRAData (tableEnvelope C) 12396 161).locationBound 12396 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12396 161).energyBound 12396 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12396 161) (d.f1 12396 161) d.f2 ≤
      32 * (((1217219017 / 250000000000000000) : ℝ) + (1624339547 / 1000000000000000000) + (390410589 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12396 161) (d.w1 12396 161)
      (d.w2 12396 161) ≤
      32 * (((6160669 / 312500000000000000) : ℝ) + (1402623449 / 100000000000000000000) + (256241991 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12396 161) (d.f1 12396 161) d.f2 ≤
      ((1217219017 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1217219017 / 250000000000000000)) * ((1624339547 / 1000000000000000000)) * (126 / 100) +
      2 * (((1624339547 / 1000000000000000000)) ^ 2 + 2 * ((1217219017 / 250000000000000000)) * ((390410589 / 1000000000000000000))) +
      6 * ((1624339547 / 1000000000000000000)) * ((390410589 / 1000000000000000000)) * (126 / 100) + 8 * ((390410589 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12396 161) (d.f1 12396 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12396 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12396 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12396 161) (d.f1 12396 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12396 161) (d.w1 12396 161) (d.w2 12396 161)
  have hwexpr0 : 0 ≤ d.w0 12396 161 + d.w1 12396 161 * √(π / 2) +
      2 * d.w2 12396 161 + energyR16 12396 *
      radiusPolynomialRoot16 (d.w0 12396 161) (d.w1 12396 161) (d.w2 12396 161) := by
    positivity
  constructor
  · change (12396 : ℝ) ^ 8 * (mA 12396 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12396 161) (d.f1 12396 161) d.f2 + locationR16 12396 *
        radiusPolynomialRoot16 (d.f0 12396 161) (d.f1 12396 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12396 : ℝ) ^ 8 * (mA 12396 : ℝ) ^ 8 *
        ((((1217219017 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1217219017 / 250000000000000000)) * ((1624339547 / 1000000000000000000)) * (126 / 100) +
          2 * (((1624339547 / 1000000000000000000)) ^ 2 + 2 * ((1217219017 / 250000000000000000)) * ((390410589 / 1000000000000000000))) +
          6 * ((1624339547 / 1000000000000000000)) * ((390410589 / 1000000000000000000)) * (126 / 100) + 8 * ((390410589 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12396) *
          (32 * (((1217219017 / 250000000000000000) : ℝ) + (1624339547 / 1000000000000000000) + (390410589 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12396 : ℝ) ^ 16 *
      (d.w0 12396 161 + d.w1 12396 161 * √(π / 2) + 2 * d.w2 12396 161 +
        energyR16 12396 * radiusPolynomialRoot16 (d.w0 12396 161) (d.w1 12396 161)
          (d.w2 12396 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12396 : ℝ) ^ 16 *
        (((6160669 / 312500000000000000) : ℝ) + ((1402623449 / 100000000000000000000)) * (126 / 100) + 2 * ((256241991 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12396) *
          (32 * (((6160669 / 312500000000000000) : ℝ) + (1402623449 / 100000000000000000000) + (256241991 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12396

/-! A coarse bound on the actual paper statistics constant at dimension 12397. -/
namespace BstLean.Part266.Row12397
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12395 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12395 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12395 128 ≤ (12649 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12649 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12397) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12397 : ℕ))
    (by norm_num : (12397 : ℕ) ≤ 16384)
  have ht : paperTail256 12397 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12397 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12397 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12397 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12397 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12397 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12395 128 * √(2 / (12397 : ℝ)) *
      (√(12397 : ℝ) + paperT0 12397 + paperTail256 12397) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12397 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12397 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12397 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12395 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12395 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12397 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12397

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12397
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12397 (61 / 100) 161 (17 / (100 * 12397)) (26 / (10 * 12397)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12397 (61 / 100) 161 (17 / (100 * 12397)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (102470789 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1653154643 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (194185051 / 31250000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12397 / 12397 * (61 / 100)) ^ 4 * inverseRadius8 (12397 - 1) /
            envelopeGap 12397 (61 / 100) 161 (17 / (100 * 12397)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12397

namespace BstLean.Part266.Row12397
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12397 161 ≤ (304243301 / 62500000000000000)
  f1 : (tableEnvelope C).f1 12397 161 ≤ (81200583 / 50000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (19516591 / 50000000000000000)
  w0 : (tableEnvelope C).w0 12397 161 ≤ (394187347 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12397 161 ≤ (701141947 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12397 161 ≤ (102471993 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (102470789 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (102470789 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1653154643 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (194185051 / 31250000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1851553 / 500000000) : ℝ) ≤ √(17 / (100 * 12397) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12397) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2263523681 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (10164751113 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12397) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12397) ≤ (114077081 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12397) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12397 * (161 : ℝ) ^ 2 + 26 / (10 * 12397) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12397) : ℝ)) (tA 12397 * 161 ^ 2 + 26 / (10 * 12397)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1851553 / 500000000))) * ((102470789 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1851553 / 500000000)) ^ 3) * ((1653154643 / 1000000000000000000000000))) + ((194185051 / 31250000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1851553 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12397) : ℝ)) d.D d.V d.P (√(tA 12397) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1851553 / 500000000)) ^ 2 * (((2263523681 / 1000000000000000)) * ((10164751113 / 250000000000000000)))) + ((194185051 / 31250000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12397) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1851553 / 500000000)) * ((102470789 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12397) : ℝ)) (tA 12397 * 161 ^ 2 + 26 / (10 * 12397)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((102470789 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1851553 / 500000000)) ^ 2) * ((1653154643 / 1000000000000000000000000)) + ((194185051 / 31250000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12397) : ℝ)) (√(26 / (10 * 12397) : ℝ)) d.D d.V d.P (√(tA 12397) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1851553 / 500000000)) * (((2263523681 / 1000000000000000)) * ((10164751113 / 250000000000000000))) + ((194185051 / 31250000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12397) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((102470789 / 20000000000000000000) : ℝ) + ((194185051 / 31250000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12397

namespace BstLean.Part266.Row12397
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12397 161 ∧
    0 ≤ (tableEnvelope C).f1 12397 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12397 161 ∧
    0 ≤ (tableEnvelope C).w1 12397 161 ∧ 0 ≤ (tableEnvelope C).w2 12397 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12397 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12397 161 ∧ 0 ≤ d.f1 12397 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12397 161 ∧ 0 ≤ d.w1 12397 161 ∧ 0 ≤ d.w2 12397 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12397 ≤ 2 * (228 / 100 : ℝ) / 12397 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12397 ≤ 2 * (370 / 100 : ℝ) / 12397 := by
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
    (completeRAData (tableEnvelope C) 12397 161).locationBound 12397 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12397 161).energyBound 12397 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12397 161) (d.f1 12397 161) d.f2 ≤
      32 * (((304243301 / 62500000000000000) : ℝ) + (81200583 / 50000000000000000) + (19516591 / 50000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12397 161) (d.w1 12397 161)
      (d.w2 12397 161) ≤
      32 * (((394187347 / 20000000000000000000) : ℝ) + (701141947 / 50000000000000000000) + (102471993 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12397 161) (d.f1 12397 161) d.f2 ≤
      ((304243301 / 62500000000000000) : ℝ) ^ 2 + 2 * ((304243301 / 62500000000000000)) * ((81200583 / 50000000000000000)) * (126 / 100) +
      2 * (((81200583 / 50000000000000000)) ^ 2 + 2 * ((304243301 / 62500000000000000)) * ((19516591 / 50000000000000000))) +
      6 * ((81200583 / 50000000000000000)) * ((19516591 / 50000000000000000)) * (126 / 100) + 8 * ((19516591 / 50000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12397 161) (d.f1 12397 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12397 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12397 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12397 161) (d.f1 12397 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12397 161) (d.w1 12397 161) (d.w2 12397 161)
  have hwexpr0 : 0 ≤ d.w0 12397 161 + d.w1 12397 161 * √(π / 2) +
      2 * d.w2 12397 161 + energyR16 12397 *
      radiusPolynomialRoot16 (d.w0 12397 161) (d.w1 12397 161) (d.w2 12397 161) := by
    positivity
  constructor
  · change (12397 : ℝ) ^ 8 * (mA 12397 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12397 161) (d.f1 12397 161) d.f2 + locationR16 12397 *
        radiusPolynomialRoot16 (d.f0 12397 161) (d.f1 12397 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12397 : ℝ) ^ 8 * (mA 12397 : ℝ) ^ 8 *
        ((((304243301 / 62500000000000000) : ℝ) ^ 2 + 2 * ((304243301 / 62500000000000000)) * ((81200583 / 50000000000000000)) * (126 / 100) +
          2 * (((81200583 / 50000000000000000)) ^ 2 + 2 * ((304243301 / 62500000000000000)) * ((19516591 / 50000000000000000))) +
          6 * ((81200583 / 50000000000000000)) * ((19516591 / 50000000000000000)) * (126 / 100) + 8 * ((19516591 / 50000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12397) *
          (32 * (((304243301 / 62500000000000000) : ℝ) + (81200583 / 50000000000000000) + (19516591 / 50000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12397 : ℝ) ^ 16 *
      (d.w0 12397 161 + d.w1 12397 161 * √(π / 2) + 2 * d.w2 12397 161 +
        energyR16 12397 * radiusPolynomialRoot16 (d.w0 12397 161) (d.w1 12397 161)
          (d.w2 12397 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12397 : ℝ) ^ 16 *
        (((394187347 / 20000000000000000000) : ℝ) + ((701141947 / 50000000000000000000)) * (126 / 100) + 2 * ((102471993 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12397) *
          (32 * (((394187347 / 20000000000000000000) : ℝ) + (701141947 / 50000000000000000000) + (102471993 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12397

/-! A coarse bound on the actual paper statistics constant at dimension 12398. -/
namespace BstLean.Part266.Row12398
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12396 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12396 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12396 128 ≤ (12650 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12650 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12398) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12398 : ℕ))
    (by norm_num : (12398 : ℕ) ≤ 16384)
  have ht : paperTail256 12398 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12398 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12398 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12398 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12398 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12398 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12396 128 * √(2 / (12398 : ℝ)) *
      (√(12398 : ℝ) + paperT0 12398 + paperTail256 12398) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12398 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12398 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12398 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12396 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12396 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12398 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12398

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12398
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12398 (61 / 100) 161 (17 / (100 * 12398)) (26 / (10 * 12398)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12398 (61 / 100) 161 (17 / (100 * 12398)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (128057493 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (66104853 / 40000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (388117073 / 62500000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12398 / 12398 * (61 / 100)) ^ 4 * inverseRadius8 (12398 - 1) /
            envelopeGap 12398 (61 / 100) 161 (17 / (100 * 12398)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12398

namespace BstLean.Part266.Row12398
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12398 161 ≤ (1216728427 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12398 161 ≤ (1623684757 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (19512659 / 50000000000000000)
  w0 : (tableEnvelope C).w0 12398 161 ≤ (1970460347 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12398 161 ≤ (1401944833 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12398 161 ≤ (128058997 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (128057493 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (128057493 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (66104853 / 40000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (388117073 / 62500000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((925739 / 250000000) : ℝ) ≤ √(17 / (100 * 12398) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12398) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1131624907 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40652445499 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12398) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12398) ≤ (114067879 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12398) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12398 * (161 : ℝ) ^ 2 + 26 / (10 * 12398) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12398) : ℝ)) (tA 12398 * 161 ^ 2 + 26 / (10 * 12398)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((925739 / 250000000))) * ((128057493 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((925739 / 250000000)) ^ 3) * ((66104853 / 40000000000000000000000))) + ((388117073 / 62500000000000000000000)) * (3 / 2 * (39895 / 100000) / ((925739 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12398) : ℝ)) d.D d.V d.P (√(tA 12398) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((925739 / 250000000)) ^ 2 * (((1131624907 / 500000000000000)) * ((40652445499 / 1000000000000000000)))) + ((388117073 / 62500000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12398) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((925739 / 250000000)) * ((128057493 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12398) : ℝ)) (tA 12398 * 161 ^ 2 + 26 / (10 * 12398)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((128057493 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((925739 / 250000000)) ^ 2) * ((66104853 / 40000000000000000000000)) + ((388117073 / 62500000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12398) : ℝ)) (√(26 / (10 * 12398) : ℝ)) d.D d.V d.P (√(tA 12398) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((925739 / 250000000)) * (((1131624907 / 500000000000000)) * ((40652445499 / 1000000000000000000))) + ((388117073 / 62500000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12398) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((128057493 / 25000000000000000000) : ℝ) + ((388117073 / 62500000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12398

namespace BstLean.Part266.Row12398
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12398 161 ∧
    0 ≤ (tableEnvelope C).f1 12398 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12398 161 ∧
    0 ≤ (tableEnvelope C).w1 12398 161 ∧ 0 ≤ (tableEnvelope C).w2 12398 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12398 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12398 161 ∧ 0 ≤ d.f1 12398 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12398 161 ∧ 0 ≤ d.w1 12398 161 ∧ 0 ≤ d.w2 12398 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12398 ≤ 2 * (228 / 100 : ℝ) / 12398 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12398 ≤ 2 * (370 / 100 : ℝ) / 12398 := by
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
    (completeRAData (tableEnvelope C) 12398 161).locationBound 12398 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12398 161).energyBound 12398 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12398 161) (d.f1 12398 161) d.f2 ≤
      32 * (((1216728427 / 250000000000000000) : ℝ) + (1623684757 / 1000000000000000000) + (19512659 / 50000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12398 161) (d.w1 12398 161)
      (d.w2 12398 161) ≤
      32 * (((1970460347 / 100000000000000000000) : ℝ) + (1401944833 / 100000000000000000000) + (128058997 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12398 161) (d.f1 12398 161) d.f2 ≤
      ((1216728427 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1216728427 / 250000000000000000)) * ((1623684757 / 1000000000000000000)) * (126 / 100) +
      2 * (((1623684757 / 1000000000000000000)) ^ 2 + 2 * ((1216728427 / 250000000000000000)) * ((19512659 / 50000000000000000))) +
      6 * ((1623684757 / 1000000000000000000)) * ((19512659 / 50000000000000000)) * (126 / 100) + 8 * ((19512659 / 50000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12398 161) (d.f1 12398 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12398 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12398 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12398 161) (d.f1 12398 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12398 161) (d.w1 12398 161) (d.w2 12398 161)
  have hwexpr0 : 0 ≤ d.w0 12398 161 + d.w1 12398 161 * √(π / 2) +
      2 * d.w2 12398 161 + energyR16 12398 *
      radiusPolynomialRoot16 (d.w0 12398 161) (d.w1 12398 161) (d.w2 12398 161) := by
    positivity
  constructor
  · change (12398 : ℝ) ^ 8 * (mA 12398 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12398 161) (d.f1 12398 161) d.f2 + locationR16 12398 *
        radiusPolynomialRoot16 (d.f0 12398 161) (d.f1 12398 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12398 : ℝ) ^ 8 * (mA 12398 : ℝ) ^ 8 *
        ((((1216728427 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1216728427 / 250000000000000000)) * ((1623684757 / 1000000000000000000)) * (126 / 100) +
          2 * (((1623684757 / 1000000000000000000)) ^ 2 + 2 * ((1216728427 / 250000000000000000)) * ((19512659 / 50000000000000000))) +
          6 * ((1623684757 / 1000000000000000000)) * ((19512659 / 50000000000000000)) * (126 / 100) + 8 * ((19512659 / 50000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12398) *
          (32 * (((1216728427 / 250000000000000000) : ℝ) + (1623684757 / 1000000000000000000) + (19512659 / 50000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12398 : ℝ) ^ 16 *
      (d.w0 12398 161 + d.w1 12398 161 * √(π / 2) + 2 * d.w2 12398 161 +
        energyR16 12398 * radiusPolynomialRoot16 (d.w0 12398 161) (d.w1 12398 161)
          (d.w2 12398 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12398 : ℝ) ^ 16 *
        (((1970460347 / 100000000000000000000) : ℝ) + ((1401944833 / 100000000000000000000)) * (126 / 100) + 2 * ((128058997 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12398) *
          (32 * (((1970460347 / 100000000000000000000) : ℝ) + (1401944833 / 100000000000000000000) + (128058997 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12398

/-! A coarse bound on the actual paper statistics constant at dimension 12399. -/
namespace BstLean.Part266.Row12399
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12397 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12397 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12397 128 ≤ (12651 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12651 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12399) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12399 : ℕ))
    (by norm_num : (12399 : ℕ) ≤ 16384)
  have ht : paperTail256 12399 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12399 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12399 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12399 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12399 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12399 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12397 128 * √(2 / (12399 : ℝ)) *
      (√(12399 : ℝ) + paperT0 12399 + paperTail256 12399) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12399 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12399 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12399 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12397 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12397 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12399 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12399

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12399
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12399 (61 / 100) 161 (17 / (100 * 12399)) (26 / (10 * 12399)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12399 (61 / 100) 161 (17 / (100 * 12399)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (512106039 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1652088221 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3102913837 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12399 / 12399 * (61 / 100)) ^ 4 * inverseRadius8 (12399 - 1) /
            envelopeGap 12399 (61 / 100) 161 (17 / (100 * 12399)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12399

namespace BstLean.Part266.Row12399
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12399 161 ≤ (4865931147 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12399 161 ≤ (811678543 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (390174459 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12399 161 ≤ (984991669 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12399 161 ≤ (1401605511 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12399 161 ≤ (512112051 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (512106039 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (512106039 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1652088221 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3102913837 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3702807 / 1000000000) : ℝ) ≤ √(17 / (100 * 12399) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12399) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2262976003 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1016147203 / 25000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12399) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12399) ≤ (2851467 / 25000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12399) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12399 * (161 : ℝ) ^ 2 + 26 / (10 * 12399) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12399) : ℝ)) (tA 12399 * 161 ^ 2 + 26 / (10 * 12399)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3702807 / 1000000000))) * ((512106039 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3702807 / 1000000000)) ^ 3) * ((1652088221 / 1000000000000000000000000))) + ((3102913837 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3702807 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12399) : ℝ)) d.D d.V d.P (√(tA 12399) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3702807 / 1000000000)) ^ 2 * (((2262976003 / 1000000000000000)) * ((1016147203 / 25000000000000000)))) + ((3102913837 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12399) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3702807 / 1000000000)) * ((512106039 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12399) : ℝ)) (tA 12399 * 161 ^ 2 + 26 / (10 * 12399)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((512106039 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3702807 / 1000000000)) ^ 2) * ((1652088221 / 1000000000000000000000000)) + ((3102913837 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12399) : ℝ)) (√(26 / (10 * 12399) : ℝ)) d.D d.V d.P (√(tA 12399) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3702807 / 1000000000)) * (((2262976003 / 1000000000000000)) * ((1016147203 / 25000000000000000))) + ((3102913837 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12399) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((512106039 / 100000000000000000000) : ℝ) + ((3102913837 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12399

namespace BstLean.Part266.Row12399
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12399 161 ∧
    0 ≤ (tableEnvelope C).f1 12399 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12399 161 ∧
    0 ≤ (tableEnvelope C).w1 12399 161 ∧ 0 ≤ (tableEnvelope C).w2 12399 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12399 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12399 161 ∧ 0 ≤ d.f1 12399 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12399 161 ∧ 0 ≤ d.w1 12399 161 ∧ 0 ≤ d.w2 12399 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12399 ≤ 2 * (228 / 100 : ℝ) / 12399 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12399 ≤ 2 * (370 / 100 : ℝ) / 12399 := by
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
    (completeRAData (tableEnvelope C) 12399 161).locationBound 12399 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12399 161).energyBound 12399 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12399 161) (d.f1 12399 161) d.f2 ≤
      32 * (((4865931147 / 1000000000000000000) : ℝ) + (811678543 / 500000000000000000) + (390174459 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12399 161) (d.w1 12399 161)
      (d.w2 12399 161) ≤
      32 * (((984991669 / 50000000000000000000) : ℝ) + (1401605511 / 100000000000000000000) + (512112051 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12399 161) (d.f1 12399 161) d.f2 ≤
      ((4865931147 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4865931147 / 1000000000000000000)) * ((811678543 / 500000000000000000)) * (126 / 100) +
      2 * (((811678543 / 500000000000000000)) ^ 2 + 2 * ((4865931147 / 1000000000000000000)) * ((390174459 / 1000000000000000000))) +
      6 * ((811678543 / 500000000000000000)) * ((390174459 / 1000000000000000000)) * (126 / 100) + 8 * ((390174459 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12399 161) (d.f1 12399 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12399 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12399 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12399 161) (d.f1 12399 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12399 161) (d.w1 12399 161) (d.w2 12399 161)
  have hwexpr0 : 0 ≤ d.w0 12399 161 + d.w1 12399 161 * √(π / 2) +
      2 * d.w2 12399 161 + energyR16 12399 *
      radiusPolynomialRoot16 (d.w0 12399 161) (d.w1 12399 161) (d.w2 12399 161) := by
    positivity
  constructor
  · change (12399 : ℝ) ^ 8 * (mA 12399 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12399 161) (d.f1 12399 161) d.f2 + locationR16 12399 *
        radiusPolynomialRoot16 (d.f0 12399 161) (d.f1 12399 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12399 : ℝ) ^ 8 * (mA 12399 : ℝ) ^ 8 *
        ((((4865931147 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4865931147 / 1000000000000000000)) * ((811678543 / 500000000000000000)) * (126 / 100) +
          2 * (((811678543 / 500000000000000000)) ^ 2 + 2 * ((4865931147 / 1000000000000000000)) * ((390174459 / 1000000000000000000))) +
          6 * ((811678543 / 500000000000000000)) * ((390174459 / 1000000000000000000)) * (126 / 100) + 8 * ((390174459 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12399) *
          (32 * (((4865931147 / 1000000000000000000) : ℝ) + (811678543 / 500000000000000000) + (390174459 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12399 : ℝ) ^ 16 *
      (d.w0 12399 161 + d.w1 12399 161 * √(π / 2) + 2 * d.w2 12399 161 +
        energyR16 12399 * radiusPolynomialRoot16 (d.w0 12399 161) (d.w1 12399 161)
          (d.w2 12399 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12399 : ℝ) ^ 16 *
        (((984991669 / 50000000000000000000) : ℝ) + ((1401605511 / 100000000000000000000)) * (126 / 100) + 2 * ((512112051 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12399) *
          (32 * (((984991669 / 50000000000000000000) : ℝ) + (1401605511 / 100000000000000000000) + (512112051 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12399
