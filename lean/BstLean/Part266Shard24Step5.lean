import BstLean.Part266Shard24Step4


/-! A coarse bound on the actual paper statistics constant at dimension 12950. -/
namespace BstLean.Part266.Row12950
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12948 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12948 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12948 128 ≤ (13202 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13202 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12950) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12950 : ℕ))
    (by norm_num : (12950 : ℕ) ≤ 16384)
  have ht : paperTail256 12950 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12950 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12950 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12950 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12950 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12950 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12948 128 * √(2 / (12950 : ℝ)) *
      (√(12950 : ℝ) + paperT0 12950 + paperTail256 12950) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12950 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12950 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12950 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12948 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12948 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12950 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12950

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12950
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12950 (61 / 100) 164 (17 / (100 * 12950)) (26 / (10 * 12950)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12950 (61 / 100) 164 (17 / (100 * 12950)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (449477121 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1388346339 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4373954081 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12950 / 12950 * (61 / 100)) ^ 4 * inverseRadius8 (12950 - 1) /
            envelopeGap 12950 (61 / 100) 164 (17 / (100 * 12950)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12950

namespace BstLean.Part266.Row12950
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12950 164 ≤ (4364707183 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12950 164 ≤ (91008767 / 62500000000000000)
  f2 : (tableEnvelope C).f2 ≤ (349983891 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12950 164 ≤ (345812063 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12950 164 ≤ (1230193427 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12950 164 ≤ (224740679 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (449477121 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (449477121 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1388346339 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4373954081 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3623177 / 1000000000) : ℝ) ≤ √(17 / (100 * 12950) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12950) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (530021887 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9315129961 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12950) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12950) ≤ (109205681 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12950) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12950 * (164 : ℝ) ^ 2 + 26 / (10 * 12950) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12950) : ℝ)) (tA 12950 * 164 ^ 2 + 26 / (10 * 12950)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3623177 / 1000000000))) * ((449477121 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3623177 / 1000000000)) ^ 3) * ((1388346339 / 1000000000000000000000000))) + ((4373954081 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3623177 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12950) : ℝ)) d.D d.V d.P (√(tA 12950) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3623177 / 1000000000)) ^ 2 * (((530021887 / 250000000000000)) * ((9315129961 / 250000000000000000)))) + ((4373954081 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12950) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3623177 / 1000000000)) * ((449477121 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12950) : ℝ)) (tA 12950 * 164 ^ 2 + 26 / (10 * 12950)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((449477121 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3623177 / 1000000000)) ^ 2) * ((1388346339 / 1000000000000000000000000)) + ((4373954081 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12950) : ℝ)) (√(26 / (10 * 12950) : ℝ)) d.D d.V d.P (√(tA 12950) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3623177 / 1000000000)) * (((530021887 / 250000000000000)) * ((9315129961 / 250000000000000000))) + ((4373954081 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12950) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((449477121 / 100000000000000000000) : ℝ) + ((4373954081 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12950

namespace BstLean.Part266.Row12950
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12950 164 ∧
    0 ≤ (tableEnvelope C).f1 12950 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12950 164 ∧
    0 ≤ (tableEnvelope C).w1 12950 164 ∧ 0 ≤ (tableEnvelope C).w2 12950 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12950 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12950 164 ∧ 0 ≤ d.f1 12950 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12950 164 ∧ 0 ≤ d.w1 12950 164 ∧ 0 ≤ d.w2 12950 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12950 ≤ 2 * (228 / 100 : ℝ) / 12950 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12950 ≤ 2 * (370 / 100 : ℝ) / 12950 := by
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
    (completeRAData (tableEnvelope C) 12950 164).locationBound 12950 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12950 164).energyBound 12950 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12950 164) (d.f1 12950 164) d.f2 ≤
      32 * (((4364707183 / 1000000000000000000) : ℝ) + (91008767 / 62500000000000000) + (349983891 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12950 164) (d.w1 12950 164)
      (d.w2 12950 164) ≤
      32 * (((345812063 / 20000000000000000000) : ℝ) + (1230193427 / 100000000000000000000) + (224740679 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12950 164) (d.f1 12950 164) d.f2 ≤
      ((4364707183 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4364707183 / 1000000000000000000)) * ((91008767 / 62500000000000000)) * (126 / 100) +
      2 * (((91008767 / 62500000000000000)) ^ 2 + 2 * ((4364707183 / 1000000000000000000)) * ((349983891 / 1000000000000000000))) +
      6 * ((91008767 / 62500000000000000)) * ((349983891 / 1000000000000000000)) * (126 / 100) + 8 * ((349983891 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12950 164) (d.f1 12950 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12950 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12950 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12950 164) (d.f1 12950 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12950 164) (d.w1 12950 164) (d.w2 12950 164)
  have hwexpr0 : 0 ≤ d.w0 12950 164 + d.w1 12950 164 * √(π / 2) +
      2 * d.w2 12950 164 + energyR16 12950 *
      radiusPolynomialRoot16 (d.w0 12950 164) (d.w1 12950 164) (d.w2 12950 164) := by
    positivity
  constructor
  · change (12950 : ℝ) ^ 8 * (mA 12950 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12950 164) (d.f1 12950 164) d.f2 + locationR16 12950 *
        radiusPolynomialRoot16 (d.f0 12950 164) (d.f1 12950 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12950 : ℝ) ^ 8 * (mA 12950 : ℝ) ^ 8 *
        ((((4364707183 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4364707183 / 1000000000000000000)) * ((91008767 / 62500000000000000)) * (126 / 100) +
          2 * (((91008767 / 62500000000000000)) ^ 2 + 2 * ((4364707183 / 1000000000000000000)) * ((349983891 / 1000000000000000000))) +
          6 * ((91008767 / 62500000000000000)) * ((349983891 / 1000000000000000000)) * (126 / 100) + 8 * ((349983891 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12950) *
          (32 * (((4364707183 / 1000000000000000000) : ℝ) + (91008767 / 62500000000000000) + (349983891 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12950 : ℝ) ^ 16 *
      (d.w0 12950 164 + d.w1 12950 164 * √(π / 2) + 2 * d.w2 12950 164 +
        energyR16 12950 * radiusPolynomialRoot16 (d.w0 12950 164) (d.w1 12950 164)
          (d.w2 12950 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12950 : ℝ) ^ 16 *
        (((345812063 / 20000000000000000000) : ℝ) + ((1230193427 / 100000000000000000000)) * (126 / 100) + 2 * ((224740679 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12950) *
          (32 * (((345812063 / 20000000000000000000) : ℝ) + (1230193427 / 100000000000000000000) + (224740679 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12950

/-! A coarse bound on the actual paper statistics constant at dimension 12951. -/
namespace BstLean.Part266.Row12951
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12949 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12949 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12949 128 ≤ (13203 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13203 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12951) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12951 : ℕ))
    (by norm_num : (12951 : ℕ) ≤ 16384)
  have ht : paperTail256 12951 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12951 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12951 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12951 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12951 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12951 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12949 128 * √(2 / (12951 : ℝ)) *
      (√(12951 : ℝ) + paperT0 12951 + paperTail256 12951) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12951 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12951 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12951 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12949 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12949 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12951 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12951

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12951
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12951 (61 / 100) 164 (17 / (100 * 12951)) (26 / (10 * 12951)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12951 (61 / 100) 164 (17 / (100 * 12951)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (224686503 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1387917573 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (874245471 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12951 / 12951 * (61 / 100)) ^ 4 * inverseRadius8 (12951 - 1) /
            envelopeGap 12951 (61 / 100) 164 (17 / (100 * 12951)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12951

namespace BstLean.Part266.Row12951
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12951 164 ≤ (2181932523 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12951 164 ≤ (18198241 / 12500000000000000)
  f2 : (tableEnvelope C).f2 ≤ (349916343 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12951 164 ≤ (432164971 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12951 164 ≤ (122990851 / 10000000000000000000)
  w2 : (tableEnvelope C).w2 12951 164 ≤ (449377241 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (224686503 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (224686503 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1387917573 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (874245471 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3623037 / 1000000000) : ℝ) ≤ √(17 / (100 * 12951) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12951) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (211984199 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (2328422861 / 62500000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12951) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12951) ≤ (109197249 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12951) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12951 * (164 : ℝ) ^ 2 + 26 / (10 * 12951) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12951) : ℝ)) (tA 12951 * 164 ^ 2 + 26 / (10 * 12951)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3623037 / 1000000000))) * ((224686503 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3623037 / 1000000000)) ^ 3) * ((1387917573 / 1000000000000000000000000))) + ((874245471 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3623037 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12951) : ℝ)) d.D d.V d.P (√(tA 12951) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3623037 / 1000000000)) ^ 2 * (((211984199 / 100000000000000)) * ((2328422861 / 62500000000000000)))) + ((874245471 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12951) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3623037 / 1000000000)) * ((224686503 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12951) : ℝ)) (tA 12951 * 164 ^ 2 + 26 / (10 * 12951)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((224686503 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3623037 / 1000000000)) ^ 2) * ((1387917573 / 1000000000000000000000000)) + ((874245471 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12951) : ℝ)) (√(26 / (10 * 12951) : ℝ)) d.D d.V d.P (√(tA 12951) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3623037 / 1000000000)) * (((211984199 / 100000000000000)) * ((2328422861 / 62500000000000000))) + ((874245471 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12951) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((224686503 / 50000000000000000000) : ℝ) + ((874245471 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12951

namespace BstLean.Part266.Row12951
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12951 164 ∧
    0 ≤ (tableEnvelope C).f1 12951 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12951 164 ∧
    0 ≤ (tableEnvelope C).w1 12951 164 ∧ 0 ≤ (tableEnvelope C).w2 12951 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12951 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12951 164 ∧ 0 ≤ d.f1 12951 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12951 164 ∧ 0 ≤ d.w1 12951 164 ∧ 0 ≤ d.w2 12951 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12951 ≤ 2 * (228 / 100 : ℝ) / 12951 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12951 ≤ 2 * (370 / 100 : ℝ) / 12951 := by
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
    (completeRAData (tableEnvelope C) 12951 164).locationBound 12951 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12951 164).energyBound 12951 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12951 164) (d.f1 12951 164) d.f2 ≤
      32 * (((2181932523 / 500000000000000000) : ℝ) + (18198241 / 12500000000000000) + (349916343 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12951 164) (d.w1 12951 164)
      (d.w2 12951 164) ≤
      32 * (((432164971 / 25000000000000000000) : ℝ) + (122990851 / 10000000000000000000) + (449377241 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12951 164) (d.f1 12951 164) d.f2 ≤
      ((2181932523 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2181932523 / 500000000000000000)) * ((18198241 / 12500000000000000)) * (126 / 100) +
      2 * (((18198241 / 12500000000000000)) ^ 2 + 2 * ((2181932523 / 500000000000000000)) * ((349916343 / 1000000000000000000))) +
      6 * ((18198241 / 12500000000000000)) * ((349916343 / 1000000000000000000)) * (126 / 100) + 8 * ((349916343 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12951 164) (d.f1 12951 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12951 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12951 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12951 164) (d.f1 12951 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12951 164) (d.w1 12951 164) (d.w2 12951 164)
  have hwexpr0 : 0 ≤ d.w0 12951 164 + d.w1 12951 164 * √(π / 2) +
      2 * d.w2 12951 164 + energyR16 12951 *
      radiusPolynomialRoot16 (d.w0 12951 164) (d.w1 12951 164) (d.w2 12951 164) := by
    positivity
  constructor
  · change (12951 : ℝ) ^ 8 * (mA 12951 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12951 164) (d.f1 12951 164) d.f2 + locationR16 12951 *
        radiusPolynomialRoot16 (d.f0 12951 164) (d.f1 12951 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12951 : ℝ) ^ 8 * (mA 12951 : ℝ) ^ 8 *
        ((((2181932523 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2181932523 / 500000000000000000)) * ((18198241 / 12500000000000000)) * (126 / 100) +
          2 * (((18198241 / 12500000000000000)) ^ 2 + 2 * ((2181932523 / 500000000000000000)) * ((349916343 / 1000000000000000000))) +
          6 * ((18198241 / 12500000000000000)) * ((349916343 / 1000000000000000000)) * (126 / 100) + 8 * ((349916343 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12951) *
          (32 * (((2181932523 / 500000000000000000) : ℝ) + (18198241 / 12500000000000000) + (349916343 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12951 : ℝ) ^ 16 *
      (d.w0 12951 164 + d.w1 12951 164 * √(π / 2) + 2 * d.w2 12951 164 +
        energyR16 12951 * radiusPolynomialRoot16 (d.w0 12951 164) (d.w1 12951 164)
          (d.w2 12951 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12951 : ℝ) ^ 16 *
        (((432164971 / 25000000000000000000) : ℝ) + ((122990851 / 10000000000000000000)) * (126 / 100) + 2 * ((449377241 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12951) *
          (32 * (((432164971 / 25000000000000000000) : ℝ) + (122990851 / 10000000000000000000) + (449377241 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12951

/-! A coarse bound on the actual paper statistics constant at dimension 12952. -/
namespace BstLean.Part266.Row12952
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12950 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12950 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12950 128 ≤ (13204 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13204 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12952) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12952 : ℕ))
    (by norm_num : (12952 : ℕ) ≤ 16384)
  have ht : paperTail256 12952 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12952 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12952 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12952 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12952 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12952 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12950 128 * √(2 / (12952 : ℝ)) *
      (√(12952 : ℝ) + paperT0 12952 + paperTail256 12952) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12952 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12952 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12952 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12950 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12950 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12952 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12952

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12952
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12952 (61 / 100) 164 (17 / (100 * 12952)) (26 / (10 * 12952)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12952 (61 / 100) 164 (17 / (100 * 12952)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (449268923 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (346872243 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4368502543 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12952 / 12952 * (61 / 100)) ^ 4 * inverseRadius8 (12952 - 1) /
            envelopeGap 12952 (61 / 100) 164 (17 / (100 * 12952)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12952

namespace BstLean.Part266.Row12952
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12952 164 ≤ (545377899 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12952 164 ≤ (11644627 / 8000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (69969763 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12952 164 ≤ (1728259589 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12952 164 ≤ (614811843 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12952 164 ≤ (89854631 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (449268923 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (449268923 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (346872243 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4368502543 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3622897 / 1000000000) : ℝ) ≤ √(17 / (100 * 12952) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12952) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2119596479 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18624506517 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12952) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12952) ≤ (54594409 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12952) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12952 * (164 : ℝ) ^ 2 + 26 / (10 * 12952) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12952) : ℝ)) (tA 12952 * 164 ^ 2 + 26 / (10 * 12952)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3622897 / 1000000000))) * ((449268923 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3622897 / 1000000000)) ^ 3) * ((346872243 / 250000000000000000000000))) + ((4368502543 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3622897 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12952) : ℝ)) d.D d.V d.P (√(tA 12952) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3622897 / 1000000000)) ^ 2 * (((2119596479 / 1000000000000000)) * ((18624506517 / 500000000000000000)))) + ((4368502543 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12952) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3622897 / 1000000000)) * ((449268923 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12952) : ℝ)) (tA 12952 * 164 ^ 2 + 26 / (10 * 12952)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((449268923 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3622897 / 1000000000)) ^ 2) * ((346872243 / 250000000000000000000000)) + ((4368502543 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12952) : ℝ)) (√(26 / (10 * 12952) : ℝ)) d.D d.V d.P (√(tA 12952) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3622897 / 1000000000)) * (((2119596479 / 1000000000000000)) * ((18624506517 / 500000000000000000))) + ((4368502543 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12952) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((449268923 / 100000000000000000000) : ℝ) + ((4368502543 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12952

namespace BstLean.Part266.Row12952
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12952 164 ∧
    0 ≤ (tableEnvelope C).f1 12952 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12952 164 ∧
    0 ≤ (tableEnvelope C).w1 12952 164 ∧ 0 ≤ (tableEnvelope C).w2 12952 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12952 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12952 164 ∧ 0 ≤ d.f1 12952 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12952 164 ∧ 0 ≤ d.w1 12952 164 ∧ 0 ≤ d.w2 12952 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12952 ≤ 2 * (228 / 100 : ℝ) / 12952 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12952 ≤ 2 * (370 / 100 : ℝ) / 12952 := by
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
    (completeRAData (tableEnvelope C) 12952 164).locationBound 12952 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12952 164).energyBound 12952 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12952 164) (d.f1 12952 164) d.f2 ≤
      32 * (((545377899 / 125000000000000000) : ℝ) + (11644627 / 8000000000000000) + (69969763 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12952 164) (d.w1 12952 164)
      (d.w2 12952 164) ≤
      32 * (((1728259589 / 100000000000000000000) : ℝ) + (614811843 / 50000000000000000000) + (89854631 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12952 164) (d.f1 12952 164) d.f2 ≤
      ((545377899 / 125000000000000000) : ℝ) ^ 2 + 2 * ((545377899 / 125000000000000000)) * ((11644627 / 8000000000000000)) * (126 / 100) +
      2 * (((11644627 / 8000000000000000)) ^ 2 + 2 * ((545377899 / 125000000000000000)) * ((69969763 / 200000000000000000))) +
      6 * ((11644627 / 8000000000000000)) * ((69969763 / 200000000000000000)) * (126 / 100) + 8 * ((69969763 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12952 164) (d.f1 12952 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12952 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12952 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12952 164) (d.f1 12952 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12952 164) (d.w1 12952 164) (d.w2 12952 164)
  have hwexpr0 : 0 ≤ d.w0 12952 164 + d.w1 12952 164 * √(π / 2) +
      2 * d.w2 12952 164 + energyR16 12952 *
      radiusPolynomialRoot16 (d.w0 12952 164) (d.w1 12952 164) (d.w2 12952 164) := by
    positivity
  constructor
  · change (12952 : ℝ) ^ 8 * (mA 12952 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12952 164) (d.f1 12952 164) d.f2 + locationR16 12952 *
        radiusPolynomialRoot16 (d.f0 12952 164) (d.f1 12952 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12952 : ℝ) ^ 8 * (mA 12952 : ℝ) ^ 8 *
        ((((545377899 / 125000000000000000) : ℝ) ^ 2 + 2 * ((545377899 / 125000000000000000)) * ((11644627 / 8000000000000000)) * (126 / 100) +
          2 * (((11644627 / 8000000000000000)) ^ 2 + 2 * ((545377899 / 125000000000000000)) * ((69969763 / 200000000000000000))) +
          6 * ((11644627 / 8000000000000000)) * ((69969763 / 200000000000000000)) * (126 / 100) + 8 * ((69969763 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12952) *
          (32 * (((545377899 / 125000000000000000) : ℝ) + (11644627 / 8000000000000000) + (69969763 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12952 : ℝ) ^ 16 *
      (d.w0 12952 164 + d.w1 12952 164 * √(π / 2) + 2 * d.w2 12952 164 +
        energyR16 12952 * radiusPolynomialRoot16 (d.w0 12952 164) (d.w1 12952 164)
          (d.w2 12952 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12952 : ℝ) ^ 16 *
        (((1728259589 / 100000000000000000000) : ℝ) + ((614811843 / 50000000000000000000)) * (126 / 100) + 2 * ((89854631 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12952) *
          (32 * (((1728259589 / 100000000000000000000) : ℝ) + (614811843 / 50000000000000000000) + (89854631 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12952

/-! A coarse bound on the actual paper statistics constant at dimension 12953. -/
namespace BstLean.Part266.Row12953
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12951 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12951 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12951 128 ≤ (13205 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13205 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12953) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12953 : ℕ))
    (by norm_num : (12953 : ℕ) ≤ 16384)
  have ht : paperTail256 12953 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12953 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12953 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12953 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12953 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12953 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12951 128 * √(2 / (12953 : ℝ)) *
      (√(12953 : ℝ) + paperT0 12953 + paperTail256 12953) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12953 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12953 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12953 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12951 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12951 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12953 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12953

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12953
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12953 (61 / 100) 164 (17 / (100 * 12953)) (26 / (10 * 12953)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12953 (61 / 100) 164 (17 / (100 * 12953)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (56145609 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (173382567 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1091444911 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12953 / 12953 * (61 / 100)) ^ 4 * inverseRadius8 (12953 - 1) /
            envelopeGap 12953 (61 / 100) 164 (17 / (100 * 12953)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12953

namespace BstLean.Part266.Row12953
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12953 164 ≤ (218109081 / 50000000000000000)
  f1 : (tableEnvelope C).f1 12953 164 ≤ (1455297559 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (174890653 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12953 164 ≤ (431964857 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12953 164 ≤ (614669477 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12953 164 ≤ (224584551 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (56145609 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (56145609 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (173382567 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1091444911 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3622757 / 1000000000) : ℝ) ≤ √(17 / (100 * 12953) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12953) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1059675507 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37243261619 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12953) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12953) ≤ (27295097 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12953) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12953 * (164 : ℝ) ^ 2 + 26 / (10 * 12953) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12953) : ℝ)) (tA 12953 * 164 ^ 2 + 26 / (10 * 12953)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3622757 / 1000000000))) * ((56145609 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3622757 / 1000000000)) ^ 3) * ((173382567 / 125000000000000000000000))) + ((1091444911 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3622757 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12953) : ℝ)) d.D d.V d.P (√(tA 12953) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3622757 / 1000000000)) ^ 2 * (((1059675507 / 500000000000000)) * ((37243261619 / 1000000000000000000)))) + ((1091444911 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12953) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3622757 / 1000000000)) * ((56145609 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12953) : ℝ)) (tA 12953 * 164 ^ 2 + 26 / (10 * 12953)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((56145609 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3622757 / 1000000000)) ^ 2) * ((173382567 / 125000000000000000000000)) + ((1091444911 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12953) : ℝ)) (√(26 / (10 * 12953) : ℝ)) d.D d.V d.P (√(tA 12953) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3622757 / 1000000000)) * (((1059675507 / 500000000000000)) * ((37243261619 / 1000000000000000000))) + ((1091444911 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12953) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((56145609 / 12500000000000000000) : ℝ) + ((1091444911 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12953

namespace BstLean.Part266.Row12953
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12953 164 ∧
    0 ≤ (tableEnvelope C).f1 12953 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12953 164 ∧
    0 ≤ (tableEnvelope C).w1 12953 164 ∧ 0 ≤ (tableEnvelope C).w2 12953 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12953 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12953 164 ∧ 0 ≤ d.f1 12953 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12953 164 ∧ 0 ≤ d.w1 12953 164 ∧ 0 ≤ d.w2 12953 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12953 ≤ 2 * (228 / 100 : ℝ) / 12953 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12953 ≤ 2 * (370 / 100 : ℝ) / 12953 := by
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
    (completeRAData (tableEnvelope C) 12953 164).locationBound 12953 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12953 164).energyBound 12953 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12953 164) (d.f1 12953 164) d.f2 ≤
      32 * (((218109081 / 50000000000000000) : ℝ) + (1455297559 / 1000000000000000000) + (174890653 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12953 164) (d.w1 12953 164)
      (d.w2 12953 164) ≤
      32 * (((431964857 / 25000000000000000000) : ℝ) + (614669477 / 50000000000000000000) + (224584551 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12953 164) (d.f1 12953 164) d.f2 ≤
      ((218109081 / 50000000000000000) : ℝ) ^ 2 + 2 * ((218109081 / 50000000000000000)) * ((1455297559 / 1000000000000000000)) * (126 / 100) +
      2 * (((1455297559 / 1000000000000000000)) ^ 2 + 2 * ((218109081 / 50000000000000000)) * ((174890653 / 500000000000000000))) +
      6 * ((1455297559 / 1000000000000000000)) * ((174890653 / 500000000000000000)) * (126 / 100) + 8 * ((174890653 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12953 164) (d.f1 12953 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12953 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12953 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12953 164) (d.f1 12953 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12953 164) (d.w1 12953 164) (d.w2 12953 164)
  have hwexpr0 : 0 ≤ d.w0 12953 164 + d.w1 12953 164 * √(π / 2) +
      2 * d.w2 12953 164 + energyR16 12953 *
      radiusPolynomialRoot16 (d.w0 12953 164) (d.w1 12953 164) (d.w2 12953 164) := by
    positivity
  constructor
  · change (12953 : ℝ) ^ 8 * (mA 12953 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12953 164) (d.f1 12953 164) d.f2 + locationR16 12953 *
        radiusPolynomialRoot16 (d.f0 12953 164) (d.f1 12953 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12953 : ℝ) ^ 8 * (mA 12953 : ℝ) ^ 8 *
        ((((218109081 / 50000000000000000) : ℝ) ^ 2 + 2 * ((218109081 / 50000000000000000)) * ((1455297559 / 1000000000000000000)) * (126 / 100) +
          2 * (((1455297559 / 1000000000000000000)) ^ 2 + 2 * ((218109081 / 50000000000000000)) * ((174890653 / 500000000000000000))) +
          6 * ((1455297559 / 1000000000000000000)) * ((174890653 / 500000000000000000)) * (126 / 100) + 8 * ((174890653 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12953) *
          (32 * (((218109081 / 50000000000000000) : ℝ) + (1455297559 / 1000000000000000000) + (174890653 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12953 : ℝ) ^ 16 *
      (d.w0 12953 164 + d.w1 12953 164 * √(π / 2) + 2 * d.w2 12953 164 +
        energyR16 12953 * radiusPolynomialRoot16 (d.w0 12953 164) (d.w1 12953 164)
          (d.w2 12953 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12953 : ℝ) ^ 16 *
        (((431964857 / 25000000000000000000) : ℝ) + ((614669477 / 50000000000000000000)) * (126 / 100) + 2 * ((224584551 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12953) *
          (32 * (((431964857 / 25000000000000000000) : ℝ) + (614669477 / 50000000000000000000) + (224584551 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12953

/-! A coarse bound on the actual paper statistics constant at dimension 12954. -/
namespace BstLean.Part266.Row12954
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12952 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12952 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12952 128 ≤ (13206 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13206 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12954) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12954 : ℕ))
    (by norm_num : (12954 : ℕ) ≤ 16384)
  have ht : paperTail256 12954 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12954 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12954 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12954 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12954 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12954 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12952 128 * √(2 / (12954 : ℝ)) *
      (√(12954 : ℝ) + paperT0 12954 + paperTail256 12954) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12954 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12954 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12954 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12952 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12952 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12954 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12954

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12954
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12954 (61 / 100) 164 (17 / (100 * 12954)) (26 / (10 * 12954)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12954 (61 / 100) 164 (17 / (100 * 12954)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (449060853 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (693316133 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (136345583 / 31250000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12954 / 12954 * (61 / 100)) ^ 4 * inverseRadius8 (12954 - 1) /
            envelopeGap 12954 (61 / 100) 164 (17 / (100 * 12954)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12954

namespace BstLean.Part266.Row12954
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12954 164 ≤ (4361340333 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12954 164 ≤ (11367319 / 7812500000000000)
  f2 : (tableEnvelope C).f2 ≤ (349713817 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12954 164 ≤ (863729701 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12954 164 ≤ (1229054317 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12954 164 ≤ (11226627 / 2500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (449060853 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (449060853 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (693316133 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (136345583 / 31250000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3622617 / 1000000000) : ℝ) ≤ √(17 / (100 * 12954) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12954) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2119105597 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7447502309 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12954) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12954) ≤ (2729299 / 25000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12954) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12954 * (164 : ℝ) ^ 2 + 26 / (10 * 12954) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12954) : ℝ)) (tA 12954 * 164 ^ 2 + 26 / (10 * 12954)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3622617 / 1000000000))) * ((449060853 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3622617 / 1000000000)) ^ 3) * ((693316133 / 500000000000000000000000))) + ((136345583 / 31250000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3622617 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12954) : ℝ)) d.D d.V d.P (√(tA 12954) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3622617 / 1000000000)) ^ 2 * (((2119105597 / 1000000000000000)) * ((7447502309 / 200000000000000000)))) + ((136345583 / 31250000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12954) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3622617 / 1000000000)) * ((449060853 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12954) : ℝ)) (tA 12954 * 164 ^ 2 + 26 / (10 * 12954)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((449060853 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3622617 / 1000000000)) ^ 2) * ((693316133 / 500000000000000000000000)) + ((136345583 / 31250000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12954) : ℝ)) (√(26 / (10 * 12954) : ℝ)) d.D d.V d.P (√(tA 12954) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3622617 / 1000000000)) * (((2119105597 / 1000000000000000)) * ((7447502309 / 200000000000000000))) + ((136345583 / 31250000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12954) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((449060853 / 100000000000000000000) : ℝ) + ((136345583 / 31250000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12954

namespace BstLean.Part266.Row12954
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12954 164 ∧
    0 ≤ (tableEnvelope C).f1 12954 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12954 164 ∧
    0 ≤ (tableEnvelope C).w1 12954 164 ∧ 0 ≤ (tableEnvelope C).w2 12954 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12954 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12954 164 ∧ 0 ≤ d.f1 12954 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12954 164 ∧ 0 ≤ d.w1 12954 164 ∧ 0 ≤ d.w2 12954 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12954 ≤ 2 * (228 / 100 : ℝ) / 12954 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12954 ≤ 2 * (370 / 100 : ℝ) / 12954 := by
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
    (completeRAData (tableEnvelope C) 12954 164).locationBound 12954 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12954 164).energyBound 12954 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12954 164) (d.f1 12954 164) d.f2 ≤
      32 * (((4361340333 / 1000000000000000000) : ℝ) + (11367319 / 7812500000000000) + (349713817 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12954 164) (d.w1 12954 164)
      (d.w2 12954 164) ≤
      32 * (((863729701 / 50000000000000000000) : ℝ) + (1229054317 / 100000000000000000000) + (11226627 / 2500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12954 164) (d.f1 12954 164) d.f2 ≤
      ((4361340333 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4361340333 / 1000000000000000000)) * ((11367319 / 7812500000000000)) * (126 / 100) +
      2 * (((11367319 / 7812500000000000)) ^ 2 + 2 * ((4361340333 / 1000000000000000000)) * ((349713817 / 1000000000000000000))) +
      6 * ((11367319 / 7812500000000000)) * ((349713817 / 1000000000000000000)) * (126 / 100) + 8 * ((349713817 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12954 164) (d.f1 12954 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12954 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12954 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12954 164) (d.f1 12954 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12954 164) (d.w1 12954 164) (d.w2 12954 164)
  have hwexpr0 : 0 ≤ d.w0 12954 164 + d.w1 12954 164 * √(π / 2) +
      2 * d.w2 12954 164 + energyR16 12954 *
      radiusPolynomialRoot16 (d.w0 12954 164) (d.w1 12954 164) (d.w2 12954 164) := by
    positivity
  constructor
  · change (12954 : ℝ) ^ 8 * (mA 12954 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12954 164) (d.f1 12954 164) d.f2 + locationR16 12954 *
        radiusPolynomialRoot16 (d.f0 12954 164) (d.f1 12954 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12954 : ℝ) ^ 8 * (mA 12954 : ℝ) ^ 8 *
        ((((4361340333 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4361340333 / 1000000000000000000)) * ((11367319 / 7812500000000000)) * (126 / 100) +
          2 * (((11367319 / 7812500000000000)) ^ 2 + 2 * ((4361340333 / 1000000000000000000)) * ((349713817 / 1000000000000000000))) +
          6 * ((11367319 / 7812500000000000)) * ((349713817 / 1000000000000000000)) * (126 / 100) + 8 * ((349713817 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12954) *
          (32 * (((4361340333 / 1000000000000000000) : ℝ) + (11367319 / 7812500000000000) + (349713817 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12954 : ℝ) ^ 16 *
      (d.w0 12954 164 + d.w1 12954 164 * √(π / 2) + 2 * d.w2 12954 164 +
        energyR16 12954 * radiusPolynomialRoot16 (d.w0 12954 164) (d.w1 12954 164)
          (d.w2 12954 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12954 : ℝ) ^ 16 *
        (((863729701 / 50000000000000000000) : ℝ) + ((1229054317 / 100000000000000000000)) * (126 / 100) + 2 * ((11226627 / 2500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12954) *
          (32 * (((863729701 / 50000000000000000000) : ℝ) + (1229054317 / 100000000000000000000) + (11226627 / 2500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12954

/-! A coarse bound on the actual paper statistics constant at dimension 12955. -/
namespace BstLean.Part266.Row12955
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12953 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12953 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12953 128 ≤ (13207 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13207 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12955) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12955 : ℕ))
    (by norm_num : (12955 : ℕ) ≤ 16384)
  have ht : paperTail256 12955 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12955 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12955 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12955 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12955 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12955 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12953 128 * √(2 / (12955 : ℝ)) *
      (√(12955 : ℝ) + paperT0 12955 + paperTail256 12955) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12955 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12955 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12955 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12953 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12953 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12955 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12955

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12955
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12955 (61 / 100) 164 (17 / (100 * 12955)) (26 / (10 * 12955)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12955 (61 / 100) 164 (17 / (100 * 12955)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (224478433 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (270743 / 195312500000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2180169789 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12955 / 12955 * (61 / 100)) ^ 4 * inverseRadius8 (12955 - 1) /
            envelopeGap 12955 (61 / 100) 164 (17 / (100 * 12955)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12955

namespace BstLean.Part266.Row12955
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12955 164 ≤ (2180249663 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12955 164 ≤ (1454736193 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (87411587 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12955 164 ≤ (172705951 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 12955 164 ≤ (1228769771 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12955 164 ≤ (44896109 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (224478433 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (224478433 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (270743 / 195312500000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2180169789 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3622477 / 1000000000) : ℝ) ≤ √(17 / (100 * 12955) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12955) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2118860227 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1163492587 / 31250000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12955) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12955) ≤ (109163533 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12955) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12955 * (164 : ℝ) ^ 2 + 26 / (10 * 12955) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12955) : ℝ)) (tA 12955 * 164 ^ 2 + 26 / (10 * 12955)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3622477 / 1000000000))) * ((224478433 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3622477 / 1000000000)) ^ 3) * ((270743 / 195312500000000000000))) + ((2180169789 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3622477 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12955) : ℝ)) d.D d.V d.P (√(tA 12955) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3622477 / 1000000000)) ^ 2 * (((2118860227 / 1000000000000000)) * ((1163492587 / 31250000000000000)))) + ((2180169789 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12955) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3622477 / 1000000000)) * ((224478433 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12955) : ℝ)) (tA 12955 * 164 ^ 2 + 26 / (10 * 12955)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((224478433 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3622477 / 1000000000)) ^ 2) * ((270743 / 195312500000000000000)) + ((2180169789 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12955) : ℝ)) (√(26 / (10 * 12955) : ℝ)) d.D d.V d.P (√(tA 12955) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3622477 / 1000000000)) * (((2118860227 / 1000000000000000)) * ((1163492587 / 31250000000000000))) + ((2180169789 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12955) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((224478433 / 50000000000000000000) : ℝ) + ((2180169789 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12955

namespace BstLean.Part266.Row12955
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12955 164 ∧
    0 ≤ (tableEnvelope C).f1 12955 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12955 164 ∧
    0 ≤ (tableEnvelope C).w1 12955 164 ∧ 0 ≤ (tableEnvelope C).w2 12955 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12955 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12955 164 ∧ 0 ≤ d.f1 12955 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12955 164 ∧ 0 ≤ d.w1 12955 164 ∧ 0 ≤ d.w2 12955 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12955 ≤ 2 * (228 / 100 : ℝ) / 12955 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12955 ≤ 2 * (370 / 100 : ℝ) / 12955 := by
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
    (completeRAData (tableEnvelope C) 12955 164).locationBound 12955 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12955 164).energyBound 12955 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12955 164) (d.f1 12955 164) d.f2 ≤
      32 * (((2180249663 / 500000000000000000) : ℝ) + (1454736193 / 1000000000000000000) + (87411587 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12955 164) (d.w1 12955 164)
      (d.w2 12955 164) ≤
      32 * (((172705951 / 10000000000000000000) : ℝ) + (1228769771 / 100000000000000000000) + (44896109 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12955 164) (d.f1 12955 164) d.f2 ≤
      ((2180249663 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2180249663 / 500000000000000000)) * ((1454736193 / 1000000000000000000)) * (126 / 100) +
      2 * (((1454736193 / 1000000000000000000)) ^ 2 + 2 * ((2180249663 / 500000000000000000)) * ((87411587 / 250000000000000000))) +
      6 * ((1454736193 / 1000000000000000000)) * ((87411587 / 250000000000000000)) * (126 / 100) + 8 * ((87411587 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12955 164) (d.f1 12955 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12955 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12955 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12955 164) (d.f1 12955 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12955 164) (d.w1 12955 164) (d.w2 12955 164)
  have hwexpr0 : 0 ≤ d.w0 12955 164 + d.w1 12955 164 * √(π / 2) +
      2 * d.w2 12955 164 + energyR16 12955 *
      radiusPolynomialRoot16 (d.w0 12955 164) (d.w1 12955 164) (d.w2 12955 164) := by
    positivity
  constructor
  · change (12955 : ℝ) ^ 8 * (mA 12955 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12955 164) (d.f1 12955 164) d.f2 + locationR16 12955 *
        radiusPolynomialRoot16 (d.f0 12955 164) (d.f1 12955 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12955 : ℝ) ^ 8 * (mA 12955 : ℝ) ^ 8 *
        ((((2180249663 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2180249663 / 500000000000000000)) * ((1454736193 / 1000000000000000000)) * (126 / 100) +
          2 * (((1454736193 / 1000000000000000000)) ^ 2 + 2 * ((2180249663 / 500000000000000000)) * ((87411587 / 250000000000000000))) +
          6 * ((1454736193 / 1000000000000000000)) * ((87411587 / 250000000000000000)) * (126 / 100) + 8 * ((87411587 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12955) *
          (32 * (((2180249663 / 500000000000000000) : ℝ) + (1454736193 / 1000000000000000000) + (87411587 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12955 : ℝ) ^ 16 *
      (d.w0 12955 164 + d.w1 12955 164 * √(π / 2) + 2 * d.w2 12955 164 +
        energyR16 12955 * radiusPolynomialRoot16 (d.w0 12955 164) (d.w1 12955 164)
          (d.w2 12955 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12955 : ℝ) ^ 16 *
        (((172705951 / 10000000000000000000) : ℝ) + ((1228769771 / 100000000000000000000)) * (126 / 100) + 2 * ((44896109 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12955) *
          (32 * (((172705951 / 10000000000000000000) : ℝ) + (1228769771 / 100000000000000000000) + (44896109 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12955

/-! A coarse bound on the actual paper statistics constant at dimension 12956. -/
namespace BstLean.Part266.Row12956
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12954 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12954 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12954 128 ≤ (13208 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13208 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12956) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12956 : ℕ))
    (by norm_num : (12956 : ℕ) ≤ 16384)
  have ht : paperTail256 12956 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12956 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12956 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12956 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12956 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12956 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12954 128 * √(2 / (12956 : ℝ)) *
      (√(12956 : ℝ) + paperT0 12956 + paperTail256 12956) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12956 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12956 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12956 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12954 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12954 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12956 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12956

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12956
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12956 (61 / 100) 164 (17 / (100 * 12956)) (26 / (10 * 12956)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12956 (61 / 100) 164 (17 / (100 * 12956)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (28053307 / 6250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1385776221 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4357622407 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12956 / 12956 * (61 / 100)) ^ 4 * inverseRadius8 (12956 - 1) /
            envelopeGap 12956 (61 / 100) 164 (17 / (100 * 12956)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12956

namespace BstLean.Part266.Row12956
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12956 164 ≤ (2179827567 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12956 164 ≤ (1454454843 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (349578803 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12956 164 ≤ (34533181 / 2000000000000000000)
  w1 : (tableEnvelope C).w1 12956 164 ≤ (1228484983 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12956 164 ≤ (224428567 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (28053307 / 6250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (28053307 / 6250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1385776221 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4357622407 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1811169 / 500000000) : ℝ) ≤ √(17 / (100 * 12956) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12956) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2118614907 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1861300769 / 50000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12956) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12956) ≤ (109155107 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12956) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12956 * (164 : ℝ) ^ 2 + 26 / (10 * 12956) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12956) : ℝ)) (tA 12956 * 164 ^ 2 + 26 / (10 * 12956)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1811169 / 500000000))) * ((28053307 / 6250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1811169 / 500000000)) ^ 3) * ((1385776221 / 1000000000000000000000000))) + ((4357622407 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1811169 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12956) : ℝ)) d.D d.V d.P (√(tA 12956) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1811169 / 500000000)) ^ 2 * (((2118614907 / 1000000000000000)) * ((1861300769 / 50000000000000000)))) + ((4357622407 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12956) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1811169 / 500000000)) * ((28053307 / 6250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12956) : ℝ)) (tA 12956 * 164 ^ 2 + 26 / (10 * 12956)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((28053307 / 6250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1811169 / 500000000)) ^ 2) * ((1385776221 / 1000000000000000000000000)) + ((4357622407 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12956) : ℝ)) (√(26 / (10 * 12956) : ℝ)) d.D d.V d.P (√(tA 12956) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1811169 / 500000000)) * (((2118614907 / 1000000000000000)) * ((1861300769 / 50000000000000000))) + ((4357622407 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12956) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((28053307 / 6250000000000000000) : ℝ) + ((4357622407 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12956

namespace BstLean.Part266.Row12956
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12956 164 ∧
    0 ≤ (tableEnvelope C).f1 12956 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12956 164 ∧
    0 ≤ (tableEnvelope C).w1 12956 164 ∧ 0 ≤ (tableEnvelope C).w2 12956 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12956 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12956 164 ∧ 0 ≤ d.f1 12956 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12956 164 ∧ 0 ≤ d.w1 12956 164 ∧ 0 ≤ d.w2 12956 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12956 ≤ 2 * (228 / 100 : ℝ) / 12956 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12956 ≤ 2 * (370 / 100 : ℝ) / 12956 := by
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
    (completeRAData (tableEnvelope C) 12956 164).locationBound 12956 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12956 164).energyBound 12956 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12956 164) (d.f1 12956 164) d.f2 ≤
      32 * (((2179827567 / 500000000000000000) : ℝ) + (1454454843 / 1000000000000000000) + (349578803 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12956 164) (d.w1 12956 164)
      (d.w2 12956 164) ≤
      32 * (((34533181 / 2000000000000000000) : ℝ) + (1228484983 / 100000000000000000000) + (224428567 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12956 164) (d.f1 12956 164) d.f2 ≤
      ((2179827567 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2179827567 / 500000000000000000)) * ((1454454843 / 1000000000000000000)) * (126 / 100) +
      2 * (((1454454843 / 1000000000000000000)) ^ 2 + 2 * ((2179827567 / 500000000000000000)) * ((349578803 / 1000000000000000000))) +
      6 * ((1454454843 / 1000000000000000000)) * ((349578803 / 1000000000000000000)) * (126 / 100) + 8 * ((349578803 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12956 164) (d.f1 12956 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12956 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12956 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12956 164) (d.f1 12956 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12956 164) (d.w1 12956 164) (d.w2 12956 164)
  have hwexpr0 : 0 ≤ d.w0 12956 164 + d.w1 12956 164 * √(π / 2) +
      2 * d.w2 12956 164 + energyR16 12956 *
      radiusPolynomialRoot16 (d.w0 12956 164) (d.w1 12956 164) (d.w2 12956 164) := by
    positivity
  constructor
  · change (12956 : ℝ) ^ 8 * (mA 12956 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12956 164) (d.f1 12956 164) d.f2 + locationR16 12956 *
        radiusPolynomialRoot16 (d.f0 12956 164) (d.f1 12956 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12956 : ℝ) ^ 8 * (mA 12956 : ℝ) ^ 8 *
        ((((2179827567 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2179827567 / 500000000000000000)) * ((1454454843 / 1000000000000000000)) * (126 / 100) +
          2 * (((1454454843 / 1000000000000000000)) ^ 2 + 2 * ((2179827567 / 500000000000000000)) * ((349578803 / 1000000000000000000))) +
          6 * ((1454454843 / 1000000000000000000)) * ((349578803 / 1000000000000000000)) * (126 / 100) + 8 * ((349578803 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12956) *
          (32 * (((2179827567 / 500000000000000000) : ℝ) + (1454454843 / 1000000000000000000) + (349578803 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12956 : ℝ) ^ 16 *
      (d.w0 12956 164 + d.w1 12956 164 * √(π / 2) + 2 * d.w2 12956 164 +
        energyR16 12956 * radiusPolynomialRoot16 (d.w0 12956 164) (d.w1 12956 164)
          (d.w2 12956 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12956 : ℝ) ^ 16 *
        (((34533181 / 2000000000000000000) : ℝ) + ((1228484983 / 100000000000000000000)) * (126 / 100) + 2 * ((224428567 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12956) *
          (32 * (((34533181 / 2000000000000000000) : ℝ) + (1228484983 / 100000000000000000000) + (224428567 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12956

/-! A coarse bound on the actual paper statistics constant at dimension 12957. -/
namespace BstLean.Part266.Row12957
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12955 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12955 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12955 128 ≤ (13209 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13209 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12957) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12957 : ℕ))
    (by norm_num : (12957 : ℕ) ≤ 16384)
  have ht : paperTail256 12957 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12957 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12957 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12957 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12957 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12957 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12955 128 * √(2 / (12957 : ℝ)) *
      (√(12957 : ℝ) + paperT0 12957 + paperTail256 12957) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12957 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12957 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12957 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12955 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12955 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12957 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12957

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12957
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12957 (61 / 100) 164 (17 / (100 * 12957)) (26 / (10 * 12957)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12957 (61 / 100) 164 (17 / (100 * 12957)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (448748989 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (692674223 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (544363393 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12957 / 12957 * (61 / 100)) ^ 4 * inverseRadius8 (12957 - 1) /
            envelopeGap 12957 (61 / 100) 164 (17 / (100 * 12957)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12957

namespace BstLean.Part266.Row12957
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12957 164 ≤ (544851837 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12957 164 ≤ (1454174381 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (349511373 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12957 164 ≤ (431564857 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12957 164 ≤ (76762539 / 6250000000000000000)
  w2 : (tableEnvelope C).w2 12957 164 ≤ (56094151 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (448748989 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (448748989 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (692674223 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (544363393 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1811099 / 500000000) : ℝ) ≤ √(17 / (100 * 12957) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12957) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2118369631 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3722026929 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12957) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12957) ≤ (109146683 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12957) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12957 * (164 : ℝ) ^ 2 + 26 / (10 * 12957) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12957) : ℝ)) (tA 12957 * 164 ^ 2 + 26 / (10 * 12957)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1811099 / 500000000))) * ((448748989 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1811099 / 500000000)) ^ 3) * ((692674223 / 500000000000000000000000))) + ((544363393 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1811099 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12957) : ℝ)) d.D d.V d.P (√(tA 12957) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1811099 / 500000000)) ^ 2 * (((2118369631 / 1000000000000000)) * ((3722026929 / 100000000000000000)))) + ((544363393 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12957) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1811099 / 500000000)) * ((448748989 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12957) : ℝ)) (tA 12957 * 164 ^ 2 + 26 / (10 * 12957)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((448748989 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1811099 / 500000000)) ^ 2) * ((692674223 / 500000000000000000000000)) + ((544363393 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12957) : ℝ)) (√(26 / (10 * 12957) : ℝ)) d.D d.V d.P (√(tA 12957) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1811099 / 500000000)) * (((2118369631 / 1000000000000000)) * ((3722026929 / 100000000000000000))) + ((544363393 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12957) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((448748989 / 100000000000000000000) : ℝ) + ((544363393 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12957

namespace BstLean.Part266.Row12957
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12957 164 ∧
    0 ≤ (tableEnvelope C).f1 12957 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12957 164 ∧
    0 ≤ (tableEnvelope C).w1 12957 164 ∧ 0 ≤ (tableEnvelope C).w2 12957 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12957 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12957 164 ∧ 0 ≤ d.f1 12957 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12957 164 ∧ 0 ≤ d.w1 12957 164 ∧ 0 ≤ d.w2 12957 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12957 ≤ 2 * (228 / 100 : ℝ) / 12957 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12957 ≤ 2 * (370 / 100 : ℝ) / 12957 := by
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
    (completeRAData (tableEnvelope C) 12957 164).locationBound 12957 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12957 164).energyBound 12957 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12957 164) (d.f1 12957 164) d.f2 ≤
      32 * (((544851837 / 125000000000000000) : ℝ) + (1454174381 / 1000000000000000000) + (349511373 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12957 164) (d.w1 12957 164)
      (d.w2 12957 164) ≤
      32 * (((431564857 / 25000000000000000000) : ℝ) + (76762539 / 6250000000000000000) + (56094151 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12957 164) (d.f1 12957 164) d.f2 ≤
      ((544851837 / 125000000000000000) : ℝ) ^ 2 + 2 * ((544851837 / 125000000000000000)) * ((1454174381 / 1000000000000000000)) * (126 / 100) +
      2 * (((1454174381 / 1000000000000000000)) ^ 2 + 2 * ((544851837 / 125000000000000000)) * ((349511373 / 1000000000000000000))) +
      6 * ((1454174381 / 1000000000000000000)) * ((349511373 / 1000000000000000000)) * (126 / 100) + 8 * ((349511373 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12957 164) (d.f1 12957 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12957 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12957 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12957 164) (d.f1 12957 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12957 164) (d.w1 12957 164) (d.w2 12957 164)
  have hwexpr0 : 0 ≤ d.w0 12957 164 + d.w1 12957 164 * √(π / 2) +
      2 * d.w2 12957 164 + energyR16 12957 *
      radiusPolynomialRoot16 (d.w0 12957 164) (d.w1 12957 164) (d.w2 12957 164) := by
    positivity
  constructor
  · change (12957 : ℝ) ^ 8 * (mA 12957 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12957 164) (d.f1 12957 164) d.f2 + locationR16 12957 *
        radiusPolynomialRoot16 (d.f0 12957 164) (d.f1 12957 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12957 : ℝ) ^ 8 * (mA 12957 : ℝ) ^ 8 *
        ((((544851837 / 125000000000000000) : ℝ) ^ 2 + 2 * ((544851837 / 125000000000000000)) * ((1454174381 / 1000000000000000000)) * (126 / 100) +
          2 * (((1454174381 / 1000000000000000000)) ^ 2 + 2 * ((544851837 / 125000000000000000)) * ((349511373 / 1000000000000000000))) +
          6 * ((1454174381 / 1000000000000000000)) * ((349511373 / 1000000000000000000)) * (126 / 100) + 8 * ((349511373 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12957) *
          (32 * (((544851837 / 125000000000000000) : ℝ) + (1454174381 / 1000000000000000000) + (349511373 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12957 : ℝ) ^ 16 *
      (d.w0 12957 164 + d.w1 12957 164 * √(π / 2) + 2 * d.w2 12957 164 +
        energyR16 12957 * radiusPolynomialRoot16 (d.w0 12957 164) (d.w1 12957 164)
          (d.w2 12957 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12957 : ℝ) ^ 16 *
        (((431564857 / 25000000000000000000) : ℝ) + ((76762539 / 6250000000000000000)) * (126 / 100) + 2 * ((56094151 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12957) *
          (32 * (((431564857 / 25000000000000000000) : ℝ) + (76762539 / 6250000000000000000) + (56094151 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12957

/-! A coarse bound on the actual paper statistics constant at dimension 12958. -/
namespace BstLean.Part266.Row12958
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12956 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12956 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12956 128 ≤ (13210 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13210 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12958) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12958 : ℕ))
    (by norm_num : (12958 : ℕ) ≤ 16384)
  have ht : paperTail256 12958 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12958 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12958 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12958 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12958 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12958 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12956 128 * √(2 / (12958 : ℝ)) *
      (√(12958 : ℝ) + paperT0 12958 + paperTail256 12958) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12958 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12958 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12958 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12956 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12956 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12958 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12958

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12958
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12958 (61 / 100) 164 (17 / (100 * 12958)) (26 / (10 * 12958)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12958 (61 / 100) 164 (17 / (100 * 12958)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (448645099 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (346230209 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (870438757 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12958 / 12958 * (61 / 100)) ^ 4 * inverseRadius8 (12958 - 1) /
            envelopeGap 12958 (61 / 100) 164 (17 / (100 * 12958)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12958

namespace BstLean.Part266.Row12958
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12958 164 ≤ (2178987271 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12958 164 ≤ (145389401 / 100000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (87360991 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12958 164 ≤ (862929971 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12958 164 ≤ (30697909 / 2500000000000000000)
  w2 : (tableEnvelope C).w2 12958 164 ≤ (89729863 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (448645099 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (448645099 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (346230209 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (870438757 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1811029 / 500000000) : ℝ) ≤ √(17 / (100 * 12958) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12958) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (529531101 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37214524531 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12958) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12958) ≤ (5456913 / 50000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12958) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12958 * (164 : ℝ) ^ 2 + 26 / (10 * 12958) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12958) : ℝ)) (tA 12958 * 164 ^ 2 + 26 / (10 * 12958)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1811029 / 500000000))) * ((448645099 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1811029 / 500000000)) ^ 3) * ((346230209 / 250000000000000000000000))) + ((870438757 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1811029 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12958) : ℝ)) d.D d.V d.P (√(tA 12958) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1811029 / 500000000)) ^ 2 * (((529531101 / 250000000000000)) * ((37214524531 / 1000000000000000000)))) + ((870438757 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12958) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1811029 / 500000000)) * ((448645099 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12958) : ℝ)) (tA 12958 * 164 ^ 2 + 26 / (10 * 12958)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((448645099 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1811029 / 500000000)) ^ 2) * ((346230209 / 250000000000000000000000)) + ((870438757 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12958) : ℝ)) (√(26 / (10 * 12958) : ℝ)) d.D d.V d.P (√(tA 12958) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1811029 / 500000000)) * (((529531101 / 250000000000000)) * ((37214524531 / 1000000000000000000))) + ((870438757 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12958) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((448645099 / 100000000000000000000) : ℝ) + ((870438757 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12958

namespace BstLean.Part266.Row12958
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12958 164 ∧
    0 ≤ (tableEnvelope C).f1 12958 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12958 164 ∧
    0 ≤ (tableEnvelope C).w1 12958 164 ∧ 0 ≤ (tableEnvelope C).w2 12958 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12958 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12958 164 ∧ 0 ≤ d.f1 12958 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12958 164 ∧ 0 ≤ d.w1 12958 164 ∧ 0 ≤ d.w2 12958 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12958 ≤ 2 * (228 / 100 : ℝ) / 12958 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12958 ≤ 2 * (370 / 100 : ℝ) / 12958 := by
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
    (completeRAData (tableEnvelope C) 12958 164).locationBound 12958 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12958 164).energyBound 12958 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12958 164) (d.f1 12958 164) d.f2 ≤
      32 * (((2178987271 / 500000000000000000) : ℝ) + (145389401 / 100000000000000000) + (87360991 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12958 164) (d.w1 12958 164)
      (d.w2 12958 164) ≤
      32 * (((862929971 / 50000000000000000000) : ℝ) + (30697909 / 2500000000000000000) + (89729863 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12958 164) (d.f1 12958 164) d.f2 ≤
      ((2178987271 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2178987271 / 500000000000000000)) * ((145389401 / 100000000000000000)) * (126 / 100) +
      2 * (((145389401 / 100000000000000000)) ^ 2 + 2 * ((2178987271 / 500000000000000000)) * ((87360991 / 250000000000000000))) +
      6 * ((145389401 / 100000000000000000)) * ((87360991 / 250000000000000000)) * (126 / 100) + 8 * ((87360991 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12958 164) (d.f1 12958 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12958 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12958 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12958 164) (d.f1 12958 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12958 164) (d.w1 12958 164) (d.w2 12958 164)
  have hwexpr0 : 0 ≤ d.w0 12958 164 + d.w1 12958 164 * √(π / 2) +
      2 * d.w2 12958 164 + energyR16 12958 *
      radiusPolynomialRoot16 (d.w0 12958 164) (d.w1 12958 164) (d.w2 12958 164) := by
    positivity
  constructor
  · change (12958 : ℝ) ^ 8 * (mA 12958 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12958 164) (d.f1 12958 164) d.f2 + locationR16 12958 *
        radiusPolynomialRoot16 (d.f0 12958 164) (d.f1 12958 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12958 : ℝ) ^ 8 * (mA 12958 : ℝ) ^ 8 *
        ((((2178987271 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2178987271 / 500000000000000000)) * ((145389401 / 100000000000000000)) * (126 / 100) +
          2 * (((145389401 / 100000000000000000)) ^ 2 + 2 * ((2178987271 / 500000000000000000)) * ((87360991 / 250000000000000000))) +
          6 * ((145389401 / 100000000000000000)) * ((87360991 / 250000000000000000)) * (126 / 100) + 8 * ((87360991 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12958) *
          (32 * (((2178987271 / 500000000000000000) : ℝ) + (145389401 / 100000000000000000) + (87360991 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12958 : ℝ) ^ 16 *
      (d.w0 12958 164 + d.w1 12958 164 * √(π / 2) + 2 * d.w2 12958 164 +
        energyR16 12958 * radiusPolynomialRoot16 (d.w0 12958 164) (d.w1 12958 164)
          (d.w2 12958 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12958 : ℝ) ^ 16 *
        (((862929971 / 50000000000000000000) : ℝ) + ((30697909 / 2500000000000000000)) * (126 / 100) + 2 * ((89729863 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12958) *
          (32 * (((862929971 / 50000000000000000000) : ℝ) + (30697909 / 2500000000000000000) + (89729863 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12958

/-! A coarse bound on the actual paper statistics constant at dimension 12959. -/
namespace BstLean.Part266.Row12959
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12957 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12957 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12957 128 ≤ (13211 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13211 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12959) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12959 : ℕ))
    (by norm_num : (12959 : ℕ) ≤ 16384)
  have ht : paperTail256 12959 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12959 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12959 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12959 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12959 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12959 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12957 128 * √(2 / (12959 : ℝ)) *
      (√(12959 : ℝ) + paperT0 12959 + paperTail256 12959) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12959 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12959 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12959 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12957 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12957 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12959 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12959

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12959
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12959 (61 / 100) 164 (17 / (100 * 12959)) (26 / (10 * 12959)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12959 (61 / 100) 164 (17 / (100 * 12959)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (11213531 / 2500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1384493391 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4349482331 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12959 / 12959 * (61 / 100)) ^ 4 * inverseRadius8 (12959 - 1) /
            envelopeGap 12959 (61 / 100) 164 (17 / (100 * 12959)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12959

namespace BstLean.Part266.Row12959
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12959 164 ≤ (435713467 / 100000000000000000)
  f1 : (tableEnvelope C).f1 12959 164 ≤ (726806863 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (174688287 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12959 164 ≤ (1725460589 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12959 164 ≤ (306908047 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12959 164 ≤ (224272727 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (11213531 / 2500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (11213531 / 2500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1384493391 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4349482331 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1810959 / 500000000) : ℝ) ≤ √(17 / (100 * 12959) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12959) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2117879223 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37208781101 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12959) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12959) ≤ (54564919 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12959) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12959 * (164 : ℝ) ^ 2 + 26 / (10 * 12959) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12959) : ℝ)) (tA 12959 * 164 ^ 2 + 26 / (10 * 12959)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1810959 / 500000000))) * ((11213531 / 2500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1810959 / 500000000)) ^ 3) * ((1384493391 / 1000000000000000000000000))) + ((4349482331 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1810959 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12959) : ℝ)) d.D d.V d.P (√(tA 12959) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1810959 / 500000000)) ^ 2 * (((2117879223 / 1000000000000000)) * ((37208781101 / 1000000000000000000)))) + ((4349482331 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12959) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1810959 / 500000000)) * ((11213531 / 2500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12959) : ℝ)) (tA 12959 * 164 ^ 2 + 26 / (10 * 12959)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((11213531 / 2500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1810959 / 500000000)) ^ 2) * ((1384493391 / 1000000000000000000000000)) + ((4349482331 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12959) : ℝ)) (√(26 / (10 * 12959) : ℝ)) d.D d.V d.P (√(tA 12959) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1810959 / 500000000)) * (((2117879223 / 1000000000000000)) * ((37208781101 / 1000000000000000000))) + ((4349482331 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12959) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((11213531 / 2500000000000000000) : ℝ) + ((4349482331 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12959

namespace BstLean.Part266.Row12959
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12959 164 ∧
    0 ≤ (tableEnvelope C).f1 12959 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12959 164 ∧
    0 ≤ (tableEnvelope C).w1 12959 164 ∧ 0 ≤ (tableEnvelope C).w2 12959 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12959 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12959 164 ∧ 0 ≤ d.f1 12959 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12959 164 ∧ 0 ≤ d.w1 12959 164 ∧ 0 ≤ d.w2 12959 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12959 ≤ 2 * (228 / 100 : ℝ) / 12959 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12959 ≤ 2 * (370 / 100 : ℝ) / 12959 := by
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
    (completeRAData (tableEnvelope C) 12959 164).locationBound 12959 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12959 164).energyBound 12959 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12959 164) (d.f1 12959 164) d.f2 ≤
      32 * (((435713467 / 100000000000000000) : ℝ) + (726806863 / 500000000000000000) + (174688287 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12959 164) (d.w1 12959 164)
      (d.w2 12959 164) ≤
      32 * (((1725460589 / 100000000000000000000) : ℝ) + (306908047 / 25000000000000000000) + (224272727 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12959 164) (d.f1 12959 164) d.f2 ≤
      ((435713467 / 100000000000000000) : ℝ) ^ 2 + 2 * ((435713467 / 100000000000000000)) * ((726806863 / 500000000000000000)) * (126 / 100) +
      2 * (((726806863 / 500000000000000000)) ^ 2 + 2 * ((435713467 / 100000000000000000)) * ((174688287 / 500000000000000000))) +
      6 * ((726806863 / 500000000000000000)) * ((174688287 / 500000000000000000)) * (126 / 100) + 8 * ((174688287 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12959 164) (d.f1 12959 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12959 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12959 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12959 164) (d.f1 12959 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12959 164) (d.w1 12959 164) (d.w2 12959 164)
  have hwexpr0 : 0 ≤ d.w0 12959 164 + d.w1 12959 164 * √(π / 2) +
      2 * d.w2 12959 164 + energyR16 12959 *
      radiusPolynomialRoot16 (d.w0 12959 164) (d.w1 12959 164) (d.w2 12959 164) := by
    positivity
  constructor
  · change (12959 : ℝ) ^ 8 * (mA 12959 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12959 164) (d.f1 12959 164) d.f2 + locationR16 12959 *
        radiusPolynomialRoot16 (d.f0 12959 164) (d.f1 12959 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12959 : ℝ) ^ 8 * (mA 12959 : ℝ) ^ 8 *
        ((((435713467 / 100000000000000000) : ℝ) ^ 2 + 2 * ((435713467 / 100000000000000000)) * ((726806863 / 500000000000000000)) * (126 / 100) +
          2 * (((726806863 / 500000000000000000)) ^ 2 + 2 * ((435713467 / 100000000000000000)) * ((174688287 / 500000000000000000))) +
          6 * ((726806863 / 500000000000000000)) * ((174688287 / 500000000000000000)) * (126 / 100) + 8 * ((174688287 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12959) *
          (32 * (((435713467 / 100000000000000000) : ℝ) + (726806863 / 500000000000000000) + (174688287 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12959 : ℝ) ^ 16 *
      (d.w0 12959 164 + d.w1 12959 164 * √(π / 2) + 2 * d.w2 12959 164 +
        energyR16 12959 * radiusPolynomialRoot16 (d.w0 12959 164) (d.w1 12959 164)
          (d.w2 12959 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12959 : ℝ) ^ 16 *
        (((1725460589 / 100000000000000000000) : ℝ) + ((306908047 / 25000000000000000000)) * (126 / 100) + 2 * ((224272727 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12959) *
          (32 * (((1725460589 / 100000000000000000000) : ℝ) + (306908047 / 25000000000000000000) + (224272727 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12959

/-! A coarse bound on the actual paper statistics constant at dimension 12960. -/
namespace BstLean.Part266.Row12960
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12958 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12958 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12958 128 ≤ (13212 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13212 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12960) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12960 : ℕ))
    (by norm_num : (12960 : ℕ) ≤ 16384)
  have ht : paperTail256 12960 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12960 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12960 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12960 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12960 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12960 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12958 128 * √(2 / (12960 : ℝ)) *
      (√(12960 : ℝ) + paperT0 12960 + paperTail256 12960) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12960 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12960 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12960 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12958 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12958 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12960 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12960

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12960
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12960 (61 / 100) 164 (17 / (100 * 12960)) (26 / (10 * 12960)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12960 (61 / 100) 164 (17 / (100 * 12960)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (224218707 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (21626033 / 15625000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2173386389 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12960 / 12960 * (61 / 100)) ^ 4 * inverseRadius8 (12960 - 1) /
            envelopeGap 12960 (61 / 100) 164 (17 / (100 * 12960)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12960

namespace BstLean.Part266.Row12960
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12960 164 ≤ (4356291613 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12960 164 ≤ (145333273 / 100000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (349309107 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12960 164 ≤ (431265167 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12960 164 ≤ (306836943 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12960 164 ≤ (3587533 / 800000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (224218707 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (224218707 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (21626033 / 15625000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2173386389 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3621779 / 1000000000) : ℝ) ≤ √(17 / (100 * 12960) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12960) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2117634091 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4650379877 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12960) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12960) ≤ (109121417 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12960) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12960 * (164 : ℝ) ^ 2 + 26 / (10 * 12960) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12960) : ℝ)) (tA 12960 * 164 ^ 2 + 26 / (10 * 12960)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3621779 / 1000000000))) * ((224218707 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3621779 / 1000000000)) ^ 3) * ((21626033 / 15625000000000000000000))) + ((2173386389 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3621779 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12960) : ℝ)) d.D d.V d.P (√(tA 12960) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3621779 / 1000000000)) ^ 2 * (((2117634091 / 1000000000000000)) * ((4650379877 / 125000000000000000)))) + ((2173386389 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12960) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3621779 / 1000000000)) * ((224218707 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12960) : ℝ)) (tA 12960 * 164 ^ 2 + 26 / (10 * 12960)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((224218707 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3621779 / 1000000000)) ^ 2) * ((21626033 / 15625000000000000000000)) + ((2173386389 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12960) : ℝ)) (√(26 / (10 * 12960) : ℝ)) d.D d.V d.P (√(tA 12960) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3621779 / 1000000000)) * (((2117634091 / 1000000000000000)) * ((4650379877 / 125000000000000000))) + ((2173386389 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12960) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((224218707 / 50000000000000000000) : ℝ) + ((2173386389 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12960

namespace BstLean.Part266.Row12960
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12960 164 ∧
    0 ≤ (tableEnvelope C).f1 12960 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12960 164 ∧
    0 ≤ (tableEnvelope C).w1 12960 164 ∧ 0 ≤ (tableEnvelope C).w2 12960 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12960 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12960 164 ∧ 0 ≤ d.f1 12960 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12960 164 ∧ 0 ≤ d.w1 12960 164 ∧ 0 ≤ d.w2 12960 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12960 ≤ 2 * (228 / 100 : ℝ) / 12960 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12960 ≤ 2 * (370 / 100 : ℝ) / 12960 := by
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
    (completeRAData (tableEnvelope C) 12960 164).locationBound 12960 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12960 164).energyBound 12960 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12960 164) (d.f1 12960 164) d.f2 ≤
      32 * (((4356291613 / 1000000000000000000) : ℝ) + (145333273 / 100000000000000000) + (349309107 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12960 164) (d.w1 12960 164)
      (d.w2 12960 164) ≤
      32 * (((431265167 / 25000000000000000000) : ℝ) + (306836943 / 25000000000000000000) + (3587533 / 800000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12960 164) (d.f1 12960 164) d.f2 ≤
      ((4356291613 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4356291613 / 1000000000000000000)) * ((145333273 / 100000000000000000)) * (126 / 100) +
      2 * (((145333273 / 100000000000000000)) ^ 2 + 2 * ((4356291613 / 1000000000000000000)) * ((349309107 / 1000000000000000000))) +
      6 * ((145333273 / 100000000000000000)) * ((349309107 / 1000000000000000000)) * (126 / 100) + 8 * ((349309107 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12960 164) (d.f1 12960 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12960 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12960 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12960 164) (d.f1 12960 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12960 164) (d.w1 12960 164) (d.w2 12960 164)
  have hwexpr0 : 0 ≤ d.w0 12960 164 + d.w1 12960 164 * √(π / 2) +
      2 * d.w2 12960 164 + energyR16 12960 *
      radiusPolynomialRoot16 (d.w0 12960 164) (d.w1 12960 164) (d.w2 12960 164) := by
    positivity
  constructor
  · change (12960 : ℝ) ^ 8 * (mA 12960 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12960 164) (d.f1 12960 164) d.f2 + locationR16 12960 *
        radiusPolynomialRoot16 (d.f0 12960 164) (d.f1 12960 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12960 : ℝ) ^ 8 * (mA 12960 : ℝ) ^ 8 *
        ((((4356291613 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4356291613 / 1000000000000000000)) * ((145333273 / 100000000000000000)) * (126 / 100) +
          2 * (((145333273 / 100000000000000000)) ^ 2 + 2 * ((4356291613 / 1000000000000000000)) * ((349309107 / 1000000000000000000))) +
          6 * ((145333273 / 100000000000000000)) * ((349309107 / 1000000000000000000)) * (126 / 100) + 8 * ((349309107 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12960) *
          (32 * (((4356291613 / 1000000000000000000) : ℝ) + (145333273 / 100000000000000000) + (349309107 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12960 : ℝ) ^ 16 *
      (d.w0 12960 164 + d.w1 12960 164 * √(π / 2) + 2 * d.w2 12960 164 +
        energyR16 12960 * radiusPolynomialRoot16 (d.w0 12960 164) (d.w1 12960 164)
          (d.w2 12960 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12960 : ℝ) ^ 16 *
        (((431265167 / 25000000000000000000) : ℝ) + ((306836943 / 25000000000000000000)) * (126 / 100) + 2 * ((3587533 / 800000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12960) *
          (32 * (((431265167 / 25000000000000000000) : ℝ) + (306836943 / 25000000000000000000) + (3587533 / 800000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12960

/-! A coarse bound on the actual paper statistics constant at dimension 12961. -/
namespace BstLean.Part266.Row12961
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12959 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12959 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12959 128 ≤ (13213 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13213 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12961) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12961 : ℕ))
    (by norm_num : (12961 : ℕ) ≤ 16384)
  have ht : paperTail256 12961 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12961 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12961 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12961 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12961 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12961 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12959 128 * √(2 / (12961 : ℝ)) *
      (√(12961 : ℝ) + paperT0 12961 + paperTail256 12961) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12961 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12961 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12961 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12959 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12959 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12961 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12961

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12961
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12961 (61 / 100) 164 (17 / (100 * 12961)) (26 / (10 * 12961)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12961 (61 / 100) 164 (17 / (100 * 12961)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (22416681 / 5000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1383638997 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2172032563 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12961 / 12961 * (61 / 100)) ^ 4 * inverseRadius8 (12961 - 1) /
            envelopeGap 12961 (61 / 100) 164 (17 / (100 * 12961)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12961

namespace BstLean.Part266.Row12961
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12961 164 ≤ (4355452309 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12961 164 ≤ (11624421 / 8000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (349241757 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12961 164 ≤ (862330793 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12961 164 ≤ (1227063787 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12961 164 ≤ (448337829 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (22416681 / 5000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (22416681 / 5000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1383638997 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2172032563 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3621639 / 1000000000) : ℝ) ≤ √(17 / (100 * 12961) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12961) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1058694503 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37197298249 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12961) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12961) ≤ (54556499 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12961) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12961 * (164 : ℝ) ^ 2 + 26 / (10 * 12961) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12961) : ℝ)) (tA 12961 * 164 ^ 2 + 26 / (10 * 12961)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3621639 / 1000000000))) * ((22416681 / 5000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3621639 / 1000000000)) ^ 3) * ((1383638997 / 1000000000000000000000000))) + ((2172032563 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3621639 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12961) : ℝ)) d.D d.V d.P (√(tA 12961) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3621639 / 1000000000)) ^ 2 * (((1058694503 / 500000000000000)) * ((37197298249 / 1000000000000000000)))) + ((2172032563 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12961) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3621639 / 1000000000)) * ((22416681 / 5000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12961) : ℝ)) (tA 12961 * 164 ^ 2 + 26 / (10 * 12961)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((22416681 / 5000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3621639 / 1000000000)) ^ 2) * ((1383638997 / 1000000000000000000000000)) + ((2172032563 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12961) : ℝ)) (√(26 / (10 * 12961) : ℝ)) d.D d.V d.P (√(tA 12961) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3621639 / 1000000000)) * (((1058694503 / 500000000000000)) * ((37197298249 / 1000000000000000000))) + ((2172032563 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12961) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((22416681 / 5000000000000000000) : ℝ) + ((2172032563 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12961

namespace BstLean.Part266.Row12961
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12961 164 ∧
    0 ≤ (tableEnvelope C).f1 12961 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12961 164 ∧
    0 ≤ (tableEnvelope C).w1 12961 164 ∧ 0 ≤ (tableEnvelope C).w2 12961 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12961 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12961 164 ∧ 0 ≤ d.f1 12961 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12961 164 ∧ 0 ≤ d.w1 12961 164 ∧ 0 ≤ d.w2 12961 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12961 ≤ 2 * (228 / 100 : ℝ) / 12961 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12961 ≤ 2 * (370 / 100 : ℝ) / 12961 := by
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
    (completeRAData (tableEnvelope C) 12961 164).locationBound 12961 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12961 164).energyBound 12961 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12961 164) (d.f1 12961 164) d.f2 ≤
      32 * (((4355452309 / 1000000000000000000) : ℝ) + (11624421 / 8000000000000000) + (349241757 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12961 164) (d.w1 12961 164)
      (d.w2 12961 164) ≤
      32 * (((862330793 / 50000000000000000000) : ℝ) + (1227063787 / 100000000000000000000) + (448337829 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12961 164) (d.f1 12961 164) d.f2 ≤
      ((4355452309 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4355452309 / 1000000000000000000)) * ((11624421 / 8000000000000000)) * (126 / 100) +
      2 * (((11624421 / 8000000000000000)) ^ 2 + 2 * ((4355452309 / 1000000000000000000)) * ((349241757 / 1000000000000000000))) +
      6 * ((11624421 / 8000000000000000)) * ((349241757 / 1000000000000000000)) * (126 / 100) + 8 * ((349241757 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12961 164) (d.f1 12961 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12961 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12961 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12961 164) (d.f1 12961 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12961 164) (d.w1 12961 164) (d.w2 12961 164)
  have hwexpr0 : 0 ≤ d.w0 12961 164 + d.w1 12961 164 * √(π / 2) +
      2 * d.w2 12961 164 + energyR16 12961 *
      radiusPolynomialRoot16 (d.w0 12961 164) (d.w1 12961 164) (d.w2 12961 164) := by
    positivity
  constructor
  · change (12961 : ℝ) ^ 8 * (mA 12961 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12961 164) (d.f1 12961 164) d.f2 + locationR16 12961 *
        radiusPolynomialRoot16 (d.f0 12961 164) (d.f1 12961 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12961 : ℝ) ^ 8 * (mA 12961 : ℝ) ^ 8 *
        ((((4355452309 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4355452309 / 1000000000000000000)) * ((11624421 / 8000000000000000)) * (126 / 100) +
          2 * (((11624421 / 8000000000000000)) ^ 2 + 2 * ((4355452309 / 1000000000000000000)) * ((349241757 / 1000000000000000000))) +
          6 * ((11624421 / 8000000000000000)) * ((349241757 / 1000000000000000000)) * (126 / 100) + 8 * ((349241757 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12961) *
          (32 * (((4355452309 / 1000000000000000000) : ℝ) + (11624421 / 8000000000000000) + (349241757 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12961 : ℝ) ^ 16 *
      (d.w0 12961 164 + d.w1 12961 164 * √(π / 2) + 2 * d.w2 12961 164 +
        energyR16 12961 * radiusPolynomialRoot16 (d.w0 12961 164) (d.w1 12961 164)
          (d.w2 12961 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12961 : ℝ) ^ 16 *
        (((862330793 / 50000000000000000000) : ℝ) + ((1227063787 / 100000000000000000000)) * (126 / 100) + 2 * ((448337829 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12961) *
          (32 * (((862330793 / 50000000000000000000) : ℝ) + (1227063787 / 100000000000000000000) + (448337829 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12961

/-! A coarse bound on the actual paper statistics constant at dimension 12962. -/
namespace BstLean.Part266.Row12962
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12960 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12960 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12960 128 ≤ (13214 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13214 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12962) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12962 : ℕ))
    (by norm_num : (12962 : ℕ) ≤ 16384)
  have ht : paperTail256 12962 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12962 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12962 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12962 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12962 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12962 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12960 128 * √(2 / (12962 : ℝ)) *
      (√(12962 : ℝ) + paperT0 12962 + paperTail256 12962) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12962 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12962 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12962 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12960 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12960 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12962 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12962

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12962
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12962 (61 / 100) 164 (17 / (100 * 12962)) (26 / (10 * 12962)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12962 (61 / 100) 164 (17 / (100 * 12962)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (448229857 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (691606023 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4341359373 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12962 / 12962 * (61 / 100)) ^ 4 * inverseRadius8 (12962 - 1) /
            envelopeGap 12962 (61 / 100) 164 (17 / (100 * 12962)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12962

namespace BstLean.Part266.Row12962
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12962 164 ≤ (870922657 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12962 164 ≤ (726386303 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (174587213 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12962 164 ≤ (1724262637 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12962 164 ≤ (613389947 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12962 164 ≤ (448234063 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (448229857 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (448229857 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (691606023 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4341359373 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3621499 / 1000000000) : ℝ) ≤ √(17 / (100 * 12962) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12962) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1058571983 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37191558801 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12962) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12962) ≤ (5455229 / 50000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12962) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12962 * (164 : ℝ) ^ 2 + 26 / (10 * 12962) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12962) : ℝ)) (tA 12962 * 164 ^ 2 + 26 / (10 * 12962)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3621499 / 1000000000))) * ((448229857 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3621499 / 1000000000)) ^ 3) * ((691606023 / 500000000000000000000000))) + ((4341359373 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3621499 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12962) : ℝ)) d.D d.V d.P (√(tA 12962) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3621499 / 1000000000)) ^ 2 * (((1058571983 / 500000000000000)) * ((37191558801 / 1000000000000000000)))) + ((4341359373 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12962) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3621499 / 1000000000)) * ((448229857 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12962) : ℝ)) (tA 12962 * 164 ^ 2 + 26 / (10 * 12962)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((448229857 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3621499 / 1000000000)) ^ 2) * ((691606023 / 500000000000000000000000)) + ((4341359373 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12962) : ℝ)) (√(26 / (10 * 12962) : ℝ)) d.D d.V d.P (√(tA 12962) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3621499 / 1000000000)) * (((1058571983 / 500000000000000)) * ((37191558801 / 1000000000000000000))) + ((4341359373 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12962) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((448229857 / 100000000000000000000) : ℝ) + ((4341359373 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12962

namespace BstLean.Part266.Row12962
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12962 164 ∧
    0 ≤ (tableEnvelope C).f1 12962 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12962 164 ∧
    0 ≤ (tableEnvelope C).w1 12962 164 ∧ 0 ≤ (tableEnvelope C).w2 12962 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12962 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12962 164 ∧ 0 ≤ d.f1 12962 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12962 164 ∧ 0 ≤ d.w1 12962 164 ∧ 0 ≤ d.w2 12962 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12962 ≤ 2 * (228 / 100 : ℝ) / 12962 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12962 ≤ 2 * (370 / 100 : ℝ) / 12962 := by
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
    (completeRAData (tableEnvelope C) 12962 164).locationBound 12962 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12962 164).energyBound 12962 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12962 164) (d.f1 12962 164) d.f2 ≤
      32 * (((870922657 / 200000000000000000) : ℝ) + (726386303 / 500000000000000000) + (174587213 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12962 164) (d.w1 12962 164)
      (d.w2 12962 164) ≤
      32 * (((1724262637 / 100000000000000000000) : ℝ) + (613389947 / 50000000000000000000) + (448234063 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12962 164) (d.f1 12962 164) d.f2 ≤
      ((870922657 / 200000000000000000) : ℝ) ^ 2 + 2 * ((870922657 / 200000000000000000)) * ((726386303 / 500000000000000000)) * (126 / 100) +
      2 * (((726386303 / 500000000000000000)) ^ 2 + 2 * ((870922657 / 200000000000000000)) * ((174587213 / 500000000000000000))) +
      6 * ((726386303 / 500000000000000000)) * ((174587213 / 500000000000000000)) * (126 / 100) + 8 * ((174587213 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12962 164) (d.f1 12962 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12962 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12962 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12962 164) (d.f1 12962 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12962 164) (d.w1 12962 164) (d.w2 12962 164)
  have hwexpr0 : 0 ≤ d.w0 12962 164 + d.w1 12962 164 * √(π / 2) +
      2 * d.w2 12962 164 + energyR16 12962 *
      radiusPolynomialRoot16 (d.w0 12962 164) (d.w1 12962 164) (d.w2 12962 164) := by
    positivity
  constructor
  · change (12962 : ℝ) ^ 8 * (mA 12962 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12962 164) (d.f1 12962 164) d.f2 + locationR16 12962 *
        radiusPolynomialRoot16 (d.f0 12962 164) (d.f1 12962 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12962 : ℝ) ^ 8 * (mA 12962 : ℝ) ^ 8 *
        ((((870922657 / 200000000000000000) : ℝ) ^ 2 + 2 * ((870922657 / 200000000000000000)) * ((726386303 / 500000000000000000)) * (126 / 100) +
          2 * (((726386303 / 500000000000000000)) ^ 2 + 2 * ((870922657 / 200000000000000000)) * ((174587213 / 500000000000000000))) +
          6 * ((726386303 / 500000000000000000)) * ((174587213 / 500000000000000000)) * (126 / 100) + 8 * ((174587213 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12962) *
          (32 * (((870922657 / 200000000000000000) : ℝ) + (726386303 / 500000000000000000) + (174587213 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12962 : ℝ) ^ 16 *
      (d.w0 12962 164 + d.w1 12962 164 * √(π / 2) + 2 * d.w2 12962 164 +
        energyR16 12962 * radiusPolynomialRoot16 (d.w0 12962 164) (d.w1 12962 164)
          (d.w2 12962 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12962 : ℝ) ^ 16 *
        (((1724262637 / 100000000000000000000) : ℝ) + ((613389947 / 50000000000000000000)) * (126 / 100) + 2 * ((448234063 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12962) *
          (32 * (((1724262637 / 100000000000000000000) : ℝ) + (613389947 / 50000000000000000000) + (448234063 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12962

/-! A coarse bound on the actual paper statistics constant at dimension 12963. -/
namespace BstLean.Part266.Row12963
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12961 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12961 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12961 128 ≤ (13215 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13215 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12963) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12963 : ℕ))
    (by norm_num : (12963 : ℕ) ≤ 16384)
  have ht : paperTail256 12963 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12963 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12963 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12963 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12963 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12963 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12961 128 * √(2 / (12963 : ℝ)) *
      (√(12963 : ℝ) + paperT0 12963 + paperTail256 12963) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12963 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12963 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12963 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12961 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12961 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12963 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12963

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12963
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12963 (61 / 100) 164 (17 / (100 * 12963)) (26 / (10 * 12963)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12963 (61 / 100) 164 (17 / (100 * 12963)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (448126127 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1382785261 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4338655519 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12963 / 12963 * (61 / 100)) ^ 4 * inverseRadius8 (12963 - 1) /
            envelopeGap 12963 (61 / 100) 164 (17 / (100 * 12963)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12963

namespace BstLean.Part266.Row12963
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12963 164 ≤ (1088443637 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12963 164 ≤ (726246339 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (69821423 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12963 164 ≤ (107741489 / 6250000000000000000)
  w1 : (tableEnvelope C).w1 12963 164 ≤ (38328003 / 3125000000000000000)
  w2 : (tableEnvelope C).w2 12963 164 ≤ (44813033 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (448126127 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (448126127 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1382785261 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4338655519 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3621359 / 1000000000) : ℝ) ≤ √(17 / (100 * 12963) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12963) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (84675959 / 40000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37185820699 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12963) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12963) ≤ (27274041 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12963) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12963 * (164 : ℝ) ^ 2 + 26 / (10 * 12963) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12963) : ℝ)) (tA 12963 * 164 ^ 2 + 26 / (10 * 12963)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3621359 / 1000000000))) * ((448126127 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3621359 / 1000000000)) ^ 3) * ((1382785261 / 1000000000000000000000000))) + ((4338655519 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3621359 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12963) : ℝ)) d.D d.V d.P (√(tA 12963) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3621359 / 1000000000)) ^ 2 * (((84675959 / 40000000000000)) * ((37185820699 / 1000000000000000000)))) + ((4338655519 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12963) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3621359 / 1000000000)) * ((448126127 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12963) : ℝ)) (tA 12963 * 164 ^ 2 + 26 / (10 * 12963)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((448126127 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3621359 / 1000000000)) ^ 2) * ((1382785261 / 1000000000000000000000000)) + ((4338655519 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12963) : ℝ)) (√(26 / (10 * 12963) : ℝ)) d.D d.V d.P (√(tA 12963) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3621359 / 1000000000)) * (((84675959 / 40000000000000)) * ((37185820699 / 1000000000000000000))) + ((4338655519 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12963) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((448126127 / 100000000000000000000) : ℝ) + ((4338655519 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12963

namespace BstLean.Part266.Row12963
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12963 164 ∧
    0 ≤ (tableEnvelope C).f1 12963 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12963 164 ∧
    0 ≤ (tableEnvelope C).w1 12963 164 ∧ 0 ≤ (tableEnvelope C).w2 12963 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12963 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12963 164 ∧ 0 ≤ d.f1 12963 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12963 164 ∧ 0 ≤ d.w1 12963 164 ∧ 0 ≤ d.w2 12963 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12963 ≤ 2 * (228 / 100 : ℝ) / 12963 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12963 ≤ 2 * (370 / 100 : ℝ) / 12963 := by
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
    (completeRAData (tableEnvelope C) 12963 164).locationBound 12963 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12963 164).energyBound 12963 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12963 164) (d.f1 12963 164) d.f2 ≤
      32 * (((1088443637 / 250000000000000000) : ℝ) + (726246339 / 500000000000000000) + (69821423 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12963 164) (d.w1 12963 164)
      (d.w2 12963 164) ≤
      32 * (((107741489 / 6250000000000000000) : ℝ) + (38328003 / 3125000000000000000) + (44813033 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12963 164) (d.f1 12963 164) d.f2 ≤
      ((1088443637 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1088443637 / 250000000000000000)) * ((726246339 / 500000000000000000)) * (126 / 100) +
      2 * (((726246339 / 500000000000000000)) ^ 2 + 2 * ((1088443637 / 250000000000000000)) * ((69821423 / 200000000000000000))) +
      6 * ((726246339 / 500000000000000000)) * ((69821423 / 200000000000000000)) * (126 / 100) + 8 * ((69821423 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12963 164) (d.f1 12963 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12963 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12963 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12963 164) (d.f1 12963 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12963 164) (d.w1 12963 164) (d.w2 12963 164)
  have hwexpr0 : 0 ≤ d.w0 12963 164 + d.w1 12963 164 * √(π / 2) +
      2 * d.w2 12963 164 + energyR16 12963 *
      radiusPolynomialRoot16 (d.w0 12963 164) (d.w1 12963 164) (d.w2 12963 164) := by
    positivity
  constructor
  · change (12963 : ℝ) ^ 8 * (mA 12963 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12963 164) (d.f1 12963 164) d.f2 + locationR16 12963 *
        radiusPolynomialRoot16 (d.f0 12963 164) (d.f1 12963 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12963 : ℝ) ^ 8 * (mA 12963 : ℝ) ^ 8 *
        ((((1088443637 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1088443637 / 250000000000000000)) * ((726246339 / 500000000000000000)) * (126 / 100) +
          2 * (((726246339 / 500000000000000000)) ^ 2 + 2 * ((1088443637 / 250000000000000000)) * ((69821423 / 200000000000000000))) +
          6 * ((726246339 / 500000000000000000)) * ((69821423 / 200000000000000000)) * (126 / 100) + 8 * ((69821423 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12963) *
          (32 * (((1088443637 / 250000000000000000) : ℝ) + (726246339 / 500000000000000000) + (69821423 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12963 : ℝ) ^ 16 *
      (d.w0 12963 164 + d.w1 12963 164 * √(π / 2) + 2 * d.w2 12963 164 +
        energyR16 12963 * radiusPolynomialRoot16 (d.w0 12963 164) (d.w1 12963 164)
          (d.w2 12963 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12963 : ℝ) ^ 16 *
        (((107741489 / 6250000000000000000) : ℝ) + ((38328003 / 3125000000000000000)) * (126 / 100) + 2 * ((44813033 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12963) *
          (32 * (((107741489 / 6250000000000000000) : ℝ) + (38328003 / 3125000000000000000) + (44813033 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12963

/-! A coarse bound on the actual paper statistics constant at dimension 12964. -/
namespace BstLean.Part266.Row12964
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12962 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12962 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12962 128 ≤ (13216 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13216 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12964) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12964 : ℕ))
    (by norm_num : (12964 : ℕ) ≤ 16384)
  have ht : paperTail256 12964 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12964 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12964 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12964 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12964 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12964 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12962 128 * √(2 / (12964 : ℝ)) *
      (√(12964 : ℝ) + paperT0 12964 + paperTail256 12964) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12964 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12964 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12964 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12962 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12962 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12964 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12964

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12964
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12964 (61 / 100) 164 (17 / (100 * 12964)) (26 / (10 * 12964)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12964 (61 / 100) 164 (17 / (100 * 12964)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (448022429 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (17279483 / 12500000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (108398839 / 25000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12964 / 12964 * (61 / 100)) ^ 4 * inverseRadius8 (12964 - 1) /
            envelopeGap 12964 (61 / 100) 164 (17 / (100 * 12964)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12964

namespace BstLean.Part266.Row12964
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12964 164 ≤ (2176466311 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12964 164 ≤ (1452212037 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (21814983 / 62500000000000000)
  w0 : (tableEnvelope C).w0 12964 164 ≤ (1723464441 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12964 164 ≤ (306553013 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12964 164 ≤ (44802663 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (448022429 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (448022429 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (17279483 / 12500000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (108398839 / 25000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((181061 / 50000000) : ℝ) ≤ √(17 / (100 * 12964) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12964) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (132290877 / 62500000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9295020979 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12964) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12964) ≤ (27271937 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12964) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12964 * (164 : ℝ) ^ 2 + 26 / (10 * 12964) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12964) : ℝ)) (tA 12964 * 164 ^ 2 + 26 / (10 * 12964)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((181061 / 50000000))) * ((448022429 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((181061 / 50000000)) ^ 3) * ((17279483 / 12500000000000000000000))) + ((108398839 / 25000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((181061 / 50000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12964) : ℝ)) d.D d.V d.P (√(tA 12964) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((181061 / 50000000)) ^ 2 * (((132290877 / 62500000000000)) * ((9295020979 / 250000000000000000)))) + ((108398839 / 25000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12964) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((181061 / 50000000)) * ((448022429 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12964) : ℝ)) (tA 12964 * 164 ^ 2 + 26 / (10 * 12964)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((448022429 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((181061 / 50000000)) ^ 2) * ((17279483 / 12500000000000000000000)) + ((108398839 / 25000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12964) : ℝ)) (√(26 / (10 * 12964) : ℝ)) d.D d.V d.P (√(tA 12964) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((181061 / 50000000)) * (((132290877 / 62500000000000)) * ((9295020979 / 250000000000000000))) + ((108398839 / 25000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12964) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((448022429 / 100000000000000000000) : ℝ) + ((108398839 / 25000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12964

namespace BstLean.Part266.Row12964
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12964 164 ∧
    0 ≤ (tableEnvelope C).f1 12964 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12964 164 ∧
    0 ≤ (tableEnvelope C).w1 12964 164 ∧ 0 ≤ (tableEnvelope C).w2 12964 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12964 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12964 164 ∧ 0 ≤ d.f1 12964 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12964 164 ∧ 0 ≤ d.w1 12964 164 ∧ 0 ≤ d.w2 12964 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12964 ≤ 2 * (228 / 100 : ℝ) / 12964 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12964 ≤ 2 * (370 / 100 : ℝ) / 12964 := by
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
    (completeRAData (tableEnvelope C) 12964 164).locationBound 12964 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12964 164).energyBound 12964 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12964 164) (d.f1 12964 164) d.f2 ≤
      32 * (((2176466311 / 500000000000000000) : ℝ) + (1452212037 / 1000000000000000000) + (21814983 / 62500000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12964 164) (d.w1 12964 164)
      (d.w2 12964 164) ≤
      32 * (((1723464441 / 100000000000000000000) : ℝ) + (306553013 / 25000000000000000000) + (44802663 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12964 164) (d.f1 12964 164) d.f2 ≤
      ((2176466311 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2176466311 / 500000000000000000)) * ((1452212037 / 1000000000000000000)) * (126 / 100) +
      2 * (((1452212037 / 1000000000000000000)) ^ 2 + 2 * ((2176466311 / 500000000000000000)) * ((21814983 / 62500000000000000))) +
      6 * ((1452212037 / 1000000000000000000)) * ((21814983 / 62500000000000000)) * (126 / 100) + 8 * ((21814983 / 62500000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12964 164) (d.f1 12964 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12964 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12964 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12964 164) (d.f1 12964 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12964 164) (d.w1 12964 164) (d.w2 12964 164)
  have hwexpr0 : 0 ≤ d.w0 12964 164 + d.w1 12964 164 * √(π / 2) +
      2 * d.w2 12964 164 + energyR16 12964 *
      radiusPolynomialRoot16 (d.w0 12964 164) (d.w1 12964 164) (d.w2 12964 164) := by
    positivity
  constructor
  · change (12964 : ℝ) ^ 8 * (mA 12964 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12964 164) (d.f1 12964 164) d.f2 + locationR16 12964 *
        radiusPolynomialRoot16 (d.f0 12964 164) (d.f1 12964 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12964 : ℝ) ^ 8 * (mA 12964 : ℝ) ^ 8 *
        ((((2176466311 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2176466311 / 500000000000000000)) * ((1452212037 / 1000000000000000000)) * (126 / 100) +
          2 * (((1452212037 / 1000000000000000000)) ^ 2 + 2 * ((2176466311 / 500000000000000000)) * ((21814983 / 62500000000000000))) +
          6 * ((1452212037 / 1000000000000000000)) * ((21814983 / 62500000000000000)) * (126 / 100) + 8 * ((21814983 / 62500000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12964) *
          (32 * (((2176466311 / 500000000000000000) : ℝ) + (1452212037 / 1000000000000000000) + (21814983 / 62500000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12964 : ℝ) ^ 16 *
      (d.w0 12964 164 + d.w1 12964 164 * √(π / 2) + 2 * d.w2 12964 164 +
        energyR16 12964 * radiusPolynomialRoot16 (d.w0 12964 164) (d.w1 12964 164)
          (d.w2 12964 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12964 : ℝ) ^ 16 *
        (((1723464441 / 100000000000000000000) : ℝ) + ((306553013 / 25000000000000000000)) * (126 / 100) + 2 * ((44802663 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12964) *
          (32 * (((1723464441 / 100000000000000000000) : ℝ) + (306553013 / 25000000000000000000) + (44802663 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12964

/-! A coarse bound on the actual paper statistics constant at dimension 12965. -/
namespace BstLean.Part266.Row12965
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12963 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12963 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12963 128 ≤ (13217 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13217 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12965) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12965 : ℕ))
    (by norm_num : (12965 : ℕ) ≤ 16384)
  have ht : paperTail256 12965 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12965 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12965 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12965 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12965 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12965 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12963 128 * √(2 / (12965 : ℝ)) *
      (√(12965 : ℝ) + paperT0 12965 + paperTail256 12965) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12965 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12965 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12965 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12963 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12963 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12965 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12965

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12965
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12965 (61 / 100) 164 (17 / (100 * 12965)) (26 / (10 * 12965)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12965 (61 / 100) 164 (17 / (100 * 12965)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (447918763 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1381932183 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (541656687 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12965 / 12965 * (61 / 100)) ^ 4 * inverseRadius8 (12965 - 1) /
            envelopeGap 12965 (61 / 100) 164 (17 / (100 * 12965)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12965

namespace BstLean.Part266.Row12965
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12965 164 ≤ (4352094447 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12965 164 ≤ (725966143 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (348972457 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12965 164 ≤ (1723065897 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12965 164 ≤ (30648211 / 2500000000000000000)
  w2 : (tableEnvelope C).w2 12965 164 ≤ (447922961 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (447918763 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (447918763 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1381932183 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (541656687 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((90527 / 25000000) : ℝ) ≤ √(17 / (100 * 12965) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12965) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (132275571 / 62500000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7434869691 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12965) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12965) ≤ (54539667 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12965) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12965 * (164 : ℝ) ^ 2 + 26 / (10 * 12965) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12965) : ℝ)) (tA 12965 * 164 ^ 2 + 26 / (10 * 12965)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((90527 / 25000000))) * ((447918763 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((90527 / 25000000)) ^ 3) * ((1381932183 / 1000000000000000000000000))) + ((541656687 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((90527 / 25000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12965) : ℝ)) d.D d.V d.P (√(tA 12965) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((90527 / 25000000)) ^ 2 * (((132275571 / 62500000000000)) * ((7434869691 / 200000000000000000)))) + ((541656687 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12965) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((90527 / 25000000)) * ((447918763 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12965) : ℝ)) (tA 12965 * 164 ^ 2 + 26 / (10 * 12965)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((447918763 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((90527 / 25000000)) ^ 2) * ((1381932183 / 1000000000000000000000000)) + ((541656687 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12965) : ℝ)) (√(26 / (10 * 12965) : ℝ)) d.D d.V d.P (√(tA 12965) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((90527 / 25000000)) * (((132275571 / 62500000000000)) * ((7434869691 / 200000000000000000))) + ((541656687 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12965) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((447918763 / 100000000000000000000) : ℝ) + ((541656687 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12965

namespace BstLean.Part266.Row12965
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12965 164 ∧
    0 ≤ (tableEnvelope C).f1 12965 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12965 164 ∧
    0 ≤ (tableEnvelope C).w1 12965 164 ∧ 0 ≤ (tableEnvelope C).w2 12965 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12965 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12965 164 ∧ 0 ≤ d.f1 12965 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12965 164 ∧ 0 ≤ d.w1 12965 164 ∧ 0 ≤ d.w2 12965 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12965 ≤ 2 * (228 / 100 : ℝ) / 12965 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12965 ≤ 2 * (370 / 100 : ℝ) / 12965 := by
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
    (completeRAData (tableEnvelope C) 12965 164).locationBound 12965 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12965 164).energyBound 12965 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12965 164) (d.f1 12965 164) d.f2 ≤
      32 * (((4352094447 / 1000000000000000000) : ℝ) + (725966143 / 500000000000000000) + (348972457 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12965 164) (d.w1 12965 164)
      (d.w2 12965 164) ≤
      32 * (((1723065897 / 100000000000000000000) : ℝ) + (30648211 / 2500000000000000000) + (447922961 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12965 164) (d.f1 12965 164) d.f2 ≤
      ((4352094447 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4352094447 / 1000000000000000000)) * ((725966143 / 500000000000000000)) * (126 / 100) +
      2 * (((725966143 / 500000000000000000)) ^ 2 + 2 * ((4352094447 / 1000000000000000000)) * ((348972457 / 1000000000000000000))) +
      6 * ((725966143 / 500000000000000000)) * ((348972457 / 1000000000000000000)) * (126 / 100) + 8 * ((348972457 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12965 164) (d.f1 12965 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12965 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12965 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12965 164) (d.f1 12965 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12965 164) (d.w1 12965 164) (d.w2 12965 164)
  have hwexpr0 : 0 ≤ d.w0 12965 164 + d.w1 12965 164 * √(π / 2) +
      2 * d.w2 12965 164 + energyR16 12965 *
      radiusPolynomialRoot16 (d.w0 12965 164) (d.w1 12965 164) (d.w2 12965 164) := by
    positivity
  constructor
  · change (12965 : ℝ) ^ 8 * (mA 12965 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12965 164) (d.f1 12965 164) d.f2 + locationR16 12965 *
        radiusPolynomialRoot16 (d.f0 12965 164) (d.f1 12965 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12965 : ℝ) ^ 8 * (mA 12965 : ℝ) ^ 8 *
        ((((4352094447 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4352094447 / 1000000000000000000)) * ((725966143 / 500000000000000000)) * (126 / 100) +
          2 * (((725966143 / 500000000000000000)) ^ 2 + 2 * ((4352094447 / 1000000000000000000)) * ((348972457 / 1000000000000000000))) +
          6 * ((725966143 / 500000000000000000)) * ((348972457 / 1000000000000000000)) * (126 / 100) + 8 * ((348972457 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12965) *
          (32 * (((4352094447 / 1000000000000000000) : ℝ) + (725966143 / 500000000000000000) + (348972457 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12965 : ℝ) ^ 16 *
      (d.w0 12965 164 + d.w1 12965 164 * √(π / 2) + 2 * d.w2 12965 164 +
        energyR16 12965 * radiusPolynomialRoot16 (d.w0 12965 164) (d.w1 12965 164)
          (d.w2 12965 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12965 : ℝ) ^ 16 *
        (((1723065897 / 100000000000000000000) : ℝ) + ((30648211 / 2500000000000000000)) * (126 / 100) + 2 * ((447922961 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12965) *
          (32 * (((1723065897 / 100000000000000000000) : ℝ) + (30648211 / 2500000000000000000) + (447922961 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12965

/-! A coarse bound on the actual paper statistics constant at dimension 12966. -/
namespace BstLean.Part266.Row12966
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12964 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12964 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12964 128 ≤ (13218 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13218 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12966) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12966 : ℕ))
    (by norm_num : (12966 : ℕ) ≤ 16384)
  have ht : paperTail256 12966 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12966 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12966 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12966 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12966 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12966 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12964 128 * √(2 / (12966 : ℝ)) *
      (√(12966 : ℝ) + paperT0 12966 + paperTail256 12966) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12966 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12966 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12966 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12964 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12964 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12966 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12966

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12966
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12966 (61 / 100) 164 (17 / (100 * 12966)) (26 / (10 * 12966)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12966 (61 / 100) 164 (17 / (100 * 12966)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (447815129 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1381505891 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (173222213 / 40000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12966 / 12966 * (61 / 100)) ^ 4 * inverseRadius8 (12966 - 1) /
            envelopeGap 12966 (61 / 100) 164 (17 / (100 * 12966)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12966

namespace BstLean.Part266.Row12966
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12966 164 ≤ (4351253087 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12966 164 ≤ (725825911 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (348905109 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12966 164 ≤ (1722666783 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12966 164 ≤ (612822291 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12966 164 ≤ (111954831 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (447815129 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (447815129 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1381505891 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (173222213 / 40000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3620941 / 1000000000) : ℝ) ≤ √(17 / (100 * 12966) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12966) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (33065067 / 15625000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4646076791 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12966) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12966) ≤ (54535461 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12966) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12966 * (164 : ℝ) ^ 2 + 26 / (10 * 12966) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12966) : ℝ)) (tA 12966 * 164 ^ 2 + 26 / (10 * 12966)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3620941 / 1000000000))) * ((447815129 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3620941 / 1000000000)) ^ 3) * ((1381505891 / 1000000000000000000000000))) + ((173222213 / 40000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3620941 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12966) : ℝ)) d.D d.V d.P (√(tA 12966) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3620941 / 1000000000)) ^ 2 * (((33065067 / 15625000000000)) * ((4646076791 / 125000000000000000)))) + ((173222213 / 40000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12966) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3620941 / 1000000000)) * ((447815129 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12966) : ℝ)) (tA 12966 * 164 ^ 2 + 26 / (10 * 12966)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((447815129 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3620941 / 1000000000)) ^ 2) * ((1381505891 / 1000000000000000000000000)) + ((173222213 / 40000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12966) : ℝ)) (√(26 / (10 * 12966) : ℝ)) d.D d.V d.P (√(tA 12966) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3620941 / 1000000000)) * (((33065067 / 15625000000000)) * ((4646076791 / 125000000000000000))) + ((173222213 / 40000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12966) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((447815129 / 100000000000000000000) : ℝ) + ((173222213 / 40000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12966

namespace BstLean.Part266.Row12966
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12966 164 ∧
    0 ≤ (tableEnvelope C).f1 12966 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12966 164 ∧
    0 ≤ (tableEnvelope C).w1 12966 164 ∧ 0 ≤ (tableEnvelope C).w2 12966 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12966 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12966 164 ∧ 0 ≤ d.f1 12966 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12966 164 ∧ 0 ≤ d.w1 12966 164 ∧ 0 ≤ d.w2 12966 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12966 ≤ 2 * (228 / 100 : ℝ) / 12966 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12966 ≤ 2 * (370 / 100 : ℝ) / 12966 := by
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
    (completeRAData (tableEnvelope C) 12966 164).locationBound 12966 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12966 164).energyBound 12966 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12966 164) (d.f1 12966 164) d.f2 ≤
      32 * (((4351253087 / 1000000000000000000) : ℝ) + (725825911 / 500000000000000000) + (348905109 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12966 164) (d.w1 12966 164)
      (d.w2 12966 164) ≤
      32 * (((1722666783 / 100000000000000000000) : ℝ) + (612822291 / 50000000000000000000) + (111954831 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12966 164) (d.f1 12966 164) d.f2 ≤
      ((4351253087 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4351253087 / 1000000000000000000)) * ((725825911 / 500000000000000000)) * (126 / 100) +
      2 * (((725825911 / 500000000000000000)) ^ 2 + 2 * ((4351253087 / 1000000000000000000)) * ((348905109 / 1000000000000000000))) +
      6 * ((725825911 / 500000000000000000)) * ((348905109 / 1000000000000000000)) * (126 / 100) + 8 * ((348905109 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12966 164) (d.f1 12966 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12966 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12966 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12966 164) (d.f1 12966 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12966 164) (d.w1 12966 164) (d.w2 12966 164)
  have hwexpr0 : 0 ≤ d.w0 12966 164 + d.w1 12966 164 * √(π / 2) +
      2 * d.w2 12966 164 + energyR16 12966 *
      radiusPolynomialRoot16 (d.w0 12966 164) (d.w1 12966 164) (d.w2 12966 164) := by
    positivity
  constructor
  · change (12966 : ℝ) ^ 8 * (mA 12966 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12966 164) (d.f1 12966 164) d.f2 + locationR16 12966 *
        radiusPolynomialRoot16 (d.f0 12966 164) (d.f1 12966 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12966 : ℝ) ^ 8 * (mA 12966 : ℝ) ^ 8 *
        ((((4351253087 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4351253087 / 1000000000000000000)) * ((725825911 / 500000000000000000)) * (126 / 100) +
          2 * (((725825911 / 500000000000000000)) ^ 2 + 2 * ((4351253087 / 1000000000000000000)) * ((348905109 / 1000000000000000000))) +
          6 * ((725825911 / 500000000000000000)) * ((348905109 / 1000000000000000000)) * (126 / 100) + 8 * ((348905109 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12966) *
          (32 * (((4351253087 / 1000000000000000000) : ℝ) + (725825911 / 500000000000000000) + (348905109 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12966 : ℝ) ^ 16 *
      (d.w0 12966 164 + d.w1 12966 164 * √(π / 2) + 2 * d.w2 12966 164 +
        energyR16 12966 * radiusPolynomialRoot16 (d.w0 12966 164) (d.w1 12966 164)
          (d.w2 12966 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12966 : ℝ) ^ 16 *
        (((1722666783 / 100000000000000000000) : ℝ) + ((612822291 / 50000000000000000000)) * (126 / 100) + 2 * ((111954831 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12966) *
          (32 * (((1722666783 / 100000000000000000000) : ℝ) + (612822291 / 50000000000000000000) + (111954831 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12966

/-! A coarse bound on the actual paper statistics constant at dimension 12967. -/
namespace BstLean.Part266.Row12967
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12965 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12965 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12965 128 ≤ (13219 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13219 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12967) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12967 : ℕ))
    (by norm_num : (12967 : ℕ) ≤ 16384)
  have ht : paperTail256 12967 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12967 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12967 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12967 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12967 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12967 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12965 128 * √(2 / (12967 : ℝ)) *
      (√(12967 : ℝ) + paperT0 12967 + paperTail256 12967) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12967 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12967 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12967 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12965 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12965 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12967 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12967

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12967
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12967 (61 / 100) 164 (17 / (100 * 12967)) (26 / (10 * 12967)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12967 (61 / 100) 164 (17 / (100 * 12967)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (223855763 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (345269941 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4327859047 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12967 / 12967 * (61 / 100)) ^ 4 * inverseRadius8 (12967 - 1) /
            envelopeGap 12967 (61 / 100) 164 (17 / (100 * 12967)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12967

namespace BstLean.Part266.Row12967
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12967 164 ≤ (108760387 / 25000000000000000)
  f1 : (tableEnvelope C).f1 12967 164 ≤ (1451372247 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (348837877 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12967 164 ≤ (1722268507 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12967 164 ≤ (245072231 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12967 164 ≤ (447715719 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (223855763 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (223855763 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (345269941 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4327859047 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3620801 / 1000000000) : ℝ) ≤ √(17 / (100 * 12967) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12967) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (528979871 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (72583753 / 1953125000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12967) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12967) ≤ (10906251 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12967) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12967 * (164 : ℝ) ^ 2 + 26 / (10 * 12967) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12967) : ℝ)) (tA 12967 * 164 ^ 2 + 26 / (10 * 12967)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3620801 / 1000000000))) * ((223855763 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3620801 / 1000000000)) ^ 3) * ((345269941 / 250000000000000000000000))) + ((4327859047 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3620801 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12967) : ℝ)) d.D d.V d.P (√(tA 12967) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3620801 / 1000000000)) ^ 2 * (((528979871 / 250000000000000)) * ((72583753 / 1953125000000000)))) + ((4327859047 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12967) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3620801 / 1000000000)) * ((223855763 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12967) : ℝ)) (tA 12967 * 164 ^ 2 + 26 / (10 * 12967)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((223855763 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3620801 / 1000000000)) ^ 2) * ((345269941 / 250000000000000000000000)) + ((4327859047 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12967) : ℝ)) (√(26 / (10 * 12967) : ℝ)) d.D d.V d.P (√(tA 12967) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3620801 / 1000000000)) * (((528979871 / 250000000000000)) * ((72583753 / 1953125000000000))) + ((4327859047 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12967) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((223855763 / 50000000000000000000) : ℝ) + ((4327859047 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12967

namespace BstLean.Part266.Row12967
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12967 164 ∧
    0 ≤ (tableEnvelope C).f1 12967 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12967 164 ∧
    0 ≤ (tableEnvelope C).w1 12967 164 ∧ 0 ≤ (tableEnvelope C).w2 12967 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12967 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12967 164 ∧ 0 ≤ d.f1 12967 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12967 164 ∧ 0 ≤ d.w1 12967 164 ∧ 0 ≤ d.w2 12967 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12967 ≤ 2 * (228 / 100 : ℝ) / 12967 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12967 ≤ 2 * (370 / 100 : ℝ) / 12967 := by
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
    (completeRAData (tableEnvelope C) 12967 164).locationBound 12967 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12967 164).energyBound 12967 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12967 164) (d.f1 12967 164) d.f2 ≤
      32 * (((108760387 / 25000000000000000) : ℝ) + (1451372247 / 1000000000000000000) + (348837877 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12967 164) (d.w1 12967 164)
      (d.w2 12967 164) ≤
      32 * (((1722268507 / 100000000000000000000) : ℝ) + (245072231 / 20000000000000000000) + (447715719 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12967 164) (d.f1 12967 164) d.f2 ≤
      ((108760387 / 25000000000000000) : ℝ) ^ 2 + 2 * ((108760387 / 25000000000000000)) * ((1451372247 / 1000000000000000000)) * (126 / 100) +
      2 * (((1451372247 / 1000000000000000000)) ^ 2 + 2 * ((108760387 / 25000000000000000)) * ((348837877 / 1000000000000000000))) +
      6 * ((1451372247 / 1000000000000000000)) * ((348837877 / 1000000000000000000)) * (126 / 100) + 8 * ((348837877 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12967 164) (d.f1 12967 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12967 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12967 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12967 164) (d.f1 12967 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12967 164) (d.w1 12967 164) (d.w2 12967 164)
  have hwexpr0 : 0 ≤ d.w0 12967 164 + d.w1 12967 164 * √(π / 2) +
      2 * d.w2 12967 164 + energyR16 12967 *
      radiusPolynomialRoot16 (d.w0 12967 164) (d.w1 12967 164) (d.w2 12967 164) := by
    positivity
  constructor
  · change (12967 : ℝ) ^ 8 * (mA 12967 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12967 164) (d.f1 12967 164) d.f2 + locationR16 12967 *
        radiusPolynomialRoot16 (d.f0 12967 164) (d.f1 12967 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12967 : ℝ) ^ 8 * (mA 12967 : ℝ) ^ 8 *
        ((((108760387 / 25000000000000000) : ℝ) ^ 2 + 2 * ((108760387 / 25000000000000000)) * ((1451372247 / 1000000000000000000)) * (126 / 100) +
          2 * (((1451372247 / 1000000000000000000)) ^ 2 + 2 * ((108760387 / 25000000000000000)) * ((348837877 / 1000000000000000000))) +
          6 * ((1451372247 / 1000000000000000000)) * ((348837877 / 1000000000000000000)) * (126 / 100) + 8 * ((348837877 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12967) *
          (32 * (((108760387 / 25000000000000000) : ℝ) + (1451372247 / 1000000000000000000) + (348837877 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12967 : ℝ) ^ 16 *
      (d.w0 12967 164 + d.w1 12967 164 * √(π / 2) + 2 * d.w2 12967 164 +
        energyR16 12967 * radiusPolynomialRoot16 (d.w0 12967 164) (d.w1 12967 164)
          (d.w2 12967 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12967 : ℝ) ^ 16 *
        (((1722268507 / 100000000000000000000) : ℝ) + ((245072231 / 20000000000000000000)) * (126 / 100) + 2 * ((447715719 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12967) *
          (32 * (((1722268507 / 100000000000000000000) : ℝ) + (245072231 / 20000000000000000000) + (447715719 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12967

/-! A coarse bound on the actual paper statistics constant at dimension 12968. -/
namespace BstLean.Part266.Row12968
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12966 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12966 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12966 128 ≤ (13220 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13220 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12968) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12968 : ℕ))
    (by norm_num : (12968 : ℕ) ≤ 16384)
  have ht : paperTail256 12968 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12968 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12968 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12968 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12968 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12968 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12966 128 * √(2 / (12968 : ℝ)) *
      (√(12968 : ℝ) + paperT0 12968 + paperTail256 12968) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12968 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12968 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12968 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12966 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12966 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12968 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12968

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12968
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12968 (61 / 100) 164 (17 / (100 * 12968)) (26 / (10 * 12968)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12968 (61 / 100) 164 (17 / (100 * 12968)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (111901989 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (6903269 / 5000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2162582329 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12968 / 12968 * (61 / 100)) ^ 4 * inverseRadius8 (12968 - 1) /
            envelopeGap 12968 (61 / 100) 164 (17 / (100 * 12968)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12968

namespace BstLean.Part266.Row12968
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12968 164 ≤ (543697269 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12968 164 ≤ (725546381 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (69754133 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12968 164 ≤ (344374073 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12968 164 ≤ (1225077821 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12968 164 ≤ (223806073 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (111901989 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (111901989 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (6903269 / 5000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2162582329 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3620661 / 1000000000) : ℝ) ≤ √(17 / (100 * 12968) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12968) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (211567473 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37157150053 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12968) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12968) ≤ (1090541 / 10000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12968) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12968 * (164 : ℝ) ^ 2 + 26 / (10 * 12968) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12968) : ℝ)) (tA 12968 * 164 ^ 2 + 26 / (10 * 12968)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3620661 / 1000000000))) * ((111901989 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3620661 / 1000000000)) ^ 3) * ((6903269 / 5000000000000000000000))) + ((2162582329 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3620661 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12968) : ℝ)) d.D d.V d.P (√(tA 12968) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3620661 / 1000000000)) ^ 2 * (((211567473 / 100000000000000)) * ((37157150053 / 1000000000000000000)))) + ((2162582329 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12968) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3620661 / 1000000000)) * ((111901989 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12968) : ℝ)) (tA 12968 * 164 ^ 2 + 26 / (10 * 12968)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((111901989 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3620661 / 1000000000)) ^ 2) * ((6903269 / 5000000000000000000000)) + ((2162582329 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12968) : ℝ)) (√(26 / (10 * 12968) : ℝ)) d.D d.V d.P (√(tA 12968) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3620661 / 1000000000)) * (((211567473 / 100000000000000)) * ((37157150053 / 1000000000000000000))) + ((2162582329 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12968) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((111901989 / 25000000000000000000) : ℝ) + ((2162582329 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12968

namespace BstLean.Part266.Row12968
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12968 164 ∧
    0 ≤ (tableEnvelope C).f1 12968 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12968 164 ∧
    0 ≤ (tableEnvelope C).w1 12968 164 ∧ 0 ≤ (tableEnvelope C).w2 12968 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12968 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12968 164 ∧ 0 ≤ d.f1 12968 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12968 164 ∧ 0 ≤ d.w1 12968 164 ∧ 0 ≤ d.w2 12968 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12968 ≤ 2 * (228 / 100 : ℝ) / 12968 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12968 ≤ 2 * (370 / 100 : ℝ) / 12968 := by
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
    (completeRAData (tableEnvelope C) 12968 164).locationBound 12968 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12968 164).energyBound 12968 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12968 164) (d.f1 12968 164) d.f2 ≤
      32 * (((543697269 / 125000000000000000) : ℝ) + (725546381 / 500000000000000000) + (69754133 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12968 164) (d.w1 12968 164)
      (d.w2 12968 164) ≤
      32 * (((344374073 / 20000000000000000000) : ℝ) + (1225077821 / 100000000000000000000) + (223806073 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12968 164) (d.f1 12968 164) d.f2 ≤
      ((543697269 / 125000000000000000) : ℝ) ^ 2 + 2 * ((543697269 / 125000000000000000)) * ((725546381 / 500000000000000000)) * (126 / 100) +
      2 * (((725546381 / 500000000000000000)) ^ 2 + 2 * ((543697269 / 125000000000000000)) * ((69754133 / 200000000000000000))) +
      6 * ((725546381 / 500000000000000000)) * ((69754133 / 200000000000000000)) * (126 / 100) + 8 * ((69754133 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12968 164) (d.f1 12968 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12968 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12968 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12968 164) (d.f1 12968 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12968 164) (d.w1 12968 164) (d.w2 12968 164)
  have hwexpr0 : 0 ≤ d.w0 12968 164 + d.w1 12968 164 * √(π / 2) +
      2 * d.w2 12968 164 + energyR16 12968 *
      radiusPolynomialRoot16 (d.w0 12968 164) (d.w1 12968 164) (d.w2 12968 164) := by
    positivity
  constructor
  · change (12968 : ℝ) ^ 8 * (mA 12968 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12968 164) (d.f1 12968 164) d.f2 + locationR16 12968 *
        radiusPolynomialRoot16 (d.f0 12968 164) (d.f1 12968 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12968 : ℝ) ^ 8 * (mA 12968 : ℝ) ^ 8 *
        ((((543697269 / 125000000000000000) : ℝ) ^ 2 + 2 * ((543697269 / 125000000000000000)) * ((725546381 / 500000000000000000)) * (126 / 100) +
          2 * (((725546381 / 500000000000000000)) ^ 2 + 2 * ((543697269 / 125000000000000000)) * ((69754133 / 200000000000000000))) +
          6 * ((725546381 / 500000000000000000)) * ((69754133 / 200000000000000000)) * (126 / 100) + 8 * ((69754133 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12968) *
          (32 * (((543697269 / 125000000000000000) : ℝ) + (725546381 / 500000000000000000) + (69754133 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12968 : ℝ) ^ 16 *
      (d.w0 12968 164 + d.w1 12968 164 * √(π / 2) + 2 * d.w2 12968 164 +
        energyR16 12968 * radiusPolynomialRoot16 (d.w0 12968 164) (d.w1 12968 164)
          (d.w2 12968 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12968 : ℝ) ^ 16 *
        (((344374073 / 20000000000000000000) : ℝ) + ((1225077821 / 100000000000000000000)) * (126 / 100) + 2 * ((223806073 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12968) *
          (32 * (((344374073 / 20000000000000000000) : ℝ) + (1225077821 / 100000000000000000000) + (223806073 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12968

/-! A coarse bound on the actual paper statistics constant at dimension 12969. -/
namespace BstLean.Part266.Row12969
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12967 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12967 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12967 128 ≤ (13221 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13221 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12969) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12969 : ℕ))
    (by norm_num : (12969 : ℕ) ≤ 16384)
  have ht : paperTail256 12969 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12969 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12969 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12969 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12969 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12969 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12967 128 * √(2 / (12969 : ℝ)) *
      (√(12969 : ℝ) + paperT0 12969 + paperTail256 12969) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12969 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12969 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12969 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12967 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12967 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12969 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12969

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12969
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12969 (61 / 100) 164 (17 / (100 * 12969)) (26 / (10 * 12969)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12969 (61 / 100) 164 (17 / (100 * 12969)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (223752209 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1380228001 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4322472159 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12969 / 12969 * (61 / 100)) ^ 4 * inverseRadius8 (12969 - 1) /
            envelopeGap 12969 (61 / 100) 164 (17 / (100 * 12969)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12969

namespace BstLean.Part266.Row12969
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12969 164 ≤ (4348737641 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12969 164 ≤ (1450812563 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (21793961 / 62500000000000000)
  w0 : (tableEnvelope C).w0 12969 164 ≤ (344294331 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12969 164 ≤ (1224794243 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12969 164 ≤ (223754303 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (223752209 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (223752209 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1380228001 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4322472159 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1810261 / 500000000) : ℝ) ≤ √(17 / (100 * 12969) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12969) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2115430023 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18575709953 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12969) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12969) ≤ (109045691 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12969) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12969 * (164 : ℝ) ^ 2 + 26 / (10 * 12969) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12969) : ℝ)) (tA 12969 * 164 ^ 2 + 26 / (10 * 12969)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1810261 / 500000000))) * ((223752209 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1810261 / 500000000)) ^ 3) * ((1380228001 / 1000000000000000000000000))) + ((4322472159 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1810261 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12969) : ℝ)) d.D d.V d.P (√(tA 12969) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1810261 / 500000000)) ^ 2 * (((2115430023 / 1000000000000000)) * ((18575709953 / 500000000000000000)))) + ((4322472159 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12969) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1810261 / 500000000)) * ((223752209 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12969) : ℝ)) (tA 12969 * 164 ^ 2 + 26 / (10 * 12969)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((223752209 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1810261 / 500000000)) ^ 2) * ((1380228001 / 1000000000000000000000000)) + ((4322472159 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12969) : ℝ)) (√(26 / (10 * 12969) : ℝ)) d.D d.V d.P (√(tA 12969) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1810261 / 500000000)) * (((2115430023 / 1000000000000000)) * ((18575709953 / 500000000000000000))) + ((4322472159 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12969) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((223752209 / 50000000000000000000) : ℝ) + ((4322472159 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12969

namespace BstLean.Part266.Row12969
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12969 164 ∧
    0 ≤ (tableEnvelope C).f1 12969 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12969 164 ∧
    0 ≤ (tableEnvelope C).w1 12969 164 ∧ 0 ≤ (tableEnvelope C).w2 12969 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12969 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12969 164 ∧ 0 ≤ d.f1 12969 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12969 164 ∧ 0 ≤ d.w1 12969 164 ∧ 0 ≤ d.w2 12969 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12969 ≤ 2 * (228 / 100 : ℝ) / 12969 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12969 ≤ 2 * (370 / 100 : ℝ) / 12969 := by
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
    (completeRAData (tableEnvelope C) 12969 164).locationBound 12969 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12969 164).energyBound 12969 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12969 164) (d.f1 12969 164) d.f2 ≤
      32 * (((4348737641 / 1000000000000000000) : ℝ) + (1450812563 / 1000000000000000000) + (21793961 / 62500000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12969 164) (d.w1 12969 164)
      (d.w2 12969 164) ≤
      32 * (((344294331 / 20000000000000000000) : ℝ) + (1224794243 / 100000000000000000000) + (223754303 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12969 164) (d.f1 12969 164) d.f2 ≤
      ((4348737641 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4348737641 / 1000000000000000000)) * ((1450812563 / 1000000000000000000)) * (126 / 100) +
      2 * (((1450812563 / 1000000000000000000)) ^ 2 + 2 * ((4348737641 / 1000000000000000000)) * ((21793961 / 62500000000000000))) +
      6 * ((1450812563 / 1000000000000000000)) * ((21793961 / 62500000000000000)) * (126 / 100) + 8 * ((21793961 / 62500000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12969 164) (d.f1 12969 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12969 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12969 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12969 164) (d.f1 12969 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12969 164) (d.w1 12969 164) (d.w2 12969 164)
  have hwexpr0 : 0 ≤ d.w0 12969 164 + d.w1 12969 164 * √(π / 2) +
      2 * d.w2 12969 164 + energyR16 12969 *
      radiusPolynomialRoot16 (d.w0 12969 164) (d.w1 12969 164) (d.w2 12969 164) := by
    positivity
  constructor
  · change (12969 : ℝ) ^ 8 * (mA 12969 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12969 164) (d.f1 12969 164) d.f2 + locationR16 12969 *
        radiusPolynomialRoot16 (d.f0 12969 164) (d.f1 12969 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12969 : ℝ) ^ 8 * (mA 12969 : ℝ) ^ 8 *
        ((((4348737641 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4348737641 / 1000000000000000000)) * ((1450812563 / 1000000000000000000)) * (126 / 100) +
          2 * (((1450812563 / 1000000000000000000)) ^ 2 + 2 * ((4348737641 / 1000000000000000000)) * ((21793961 / 62500000000000000))) +
          6 * ((1450812563 / 1000000000000000000)) * ((21793961 / 62500000000000000)) * (126 / 100) + 8 * ((21793961 / 62500000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12969) *
          (32 * (((4348737641 / 1000000000000000000) : ℝ) + (1450812563 / 1000000000000000000) + (21793961 / 62500000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12969 : ℝ) ^ 16 *
      (d.w0 12969 164 + d.w1 12969 164 * √(π / 2) + 2 * d.w2 12969 164 +
        energyR16 12969 * radiusPolynomialRoot16 (d.w0 12969 164) (d.w1 12969 164)
          (d.w2 12969 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12969 : ℝ) ^ 16 *
        (((344294331 / 20000000000000000000) : ℝ) + ((1224794243 / 100000000000000000000)) * (126 / 100) + 2 * ((223754303 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12969) *
          (32 * (((344294331 / 20000000000000000000) : ℝ) + (1224794243 / 100000000000000000000) + (223754303 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12969

/-! A coarse bound on the actual paper statistics constant at dimension 12970. -/
namespace BstLean.Part266.Row12970
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12968 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12968 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12968 128 ≤ (13222 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13222 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12970) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12970 : ℕ))
    (by norm_num : (12970 : ℕ) ≤ 16384)
  have ht : paperTail256 12970 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12970 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12970 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12970 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12970 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12970 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12968 128 * √(2 / (12970 : ℝ)) *
      (√(12970 : ℝ) + paperT0 12970 + paperTail256 12970) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12970 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12970 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12970 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12968 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12968 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12970 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12970

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12970
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12970 (61 / 100) 164 (17 / (100 * 12970)) (26 / (10 * 12970)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12970 (61 / 100) 164 (17 / (100 * 12970)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (447400911 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (689901183 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2159890773 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12970 / 12970 * (61 / 100)) ^ 4 * inverseRadius8 (12970 - 1) /
            envelopeGap 12970 (61 / 100) 164 (17 / (100 * 12970)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12970

namespace BstLean.Part266.Row12970
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12970 164 ≤ (2173950439 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12970 164 ≤ (1450533253 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (348636203 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12970 164 ≤ (1721073781 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12970 164 ≤ (612255547 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12970 164 ≤ (55925637 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (447400911 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (447400911 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (689901183 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2159890773 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1810191 / 500000000) : ℝ) ≤ √(17 / (100 * 12970) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12970) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2115185361 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37145691083 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12970) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12970) ≤ (27259321 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12970) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12970 * (164 : ℝ) ^ 2 + 26 / (10 * 12970) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12970) : ℝ)) (tA 12970 * 164 ^ 2 + 26 / (10 * 12970)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1810191 / 500000000))) * ((447400911 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1810191 / 500000000)) ^ 3) * ((689901183 / 500000000000000000000000))) + ((2159890773 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1810191 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12970) : ℝ)) d.D d.V d.P (√(tA 12970) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1810191 / 500000000)) ^ 2 * (((2115185361 / 1000000000000000)) * ((37145691083 / 1000000000000000000)))) + ((2159890773 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12970) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1810191 / 500000000)) * ((447400911 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12970) : ℝ)) (tA 12970 * 164 ^ 2 + 26 / (10 * 12970)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((447400911 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1810191 / 500000000)) ^ 2) * ((689901183 / 500000000000000000000000)) + ((2159890773 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12970) : ℝ)) (√(26 / (10 * 12970) : ℝ)) d.D d.V d.P (√(tA 12970) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1810191 / 500000000)) * (((2115185361 / 1000000000000000)) * ((37145691083 / 1000000000000000000))) + ((2159890773 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12970) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((447400911 / 100000000000000000000) : ℝ) + ((2159890773 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12970

namespace BstLean.Part266.Row12970
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12970 164 ∧
    0 ≤ (tableEnvelope C).f1 12970 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12970 164 ∧
    0 ≤ (tableEnvelope C).w1 12970 164 ∧ 0 ≤ (tableEnvelope C).w2 12970 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12970 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12970 164 ∧ 0 ≤ d.f1 12970 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12970 164 ∧ 0 ≤ d.w1 12970 164 ∧ 0 ≤ d.w2 12970 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12970 ≤ 2 * (228 / 100 : ℝ) / 12970 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12970 ≤ 2 * (370 / 100 : ℝ) / 12970 := by
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
    (completeRAData (tableEnvelope C) 12970 164).locationBound 12970 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12970 164).energyBound 12970 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12970 164) (d.f1 12970 164) d.f2 ≤
      32 * (((2173950439 / 500000000000000000) : ℝ) + (1450533253 / 1000000000000000000) + (348636203 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12970 164) (d.w1 12970 164)
      (d.w2 12970 164) ≤
      32 * (((1721073781 / 100000000000000000000) : ℝ) + (612255547 / 50000000000000000000) + (55925637 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12970 164) (d.f1 12970 164) d.f2 ≤
      ((2173950439 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2173950439 / 500000000000000000)) * ((1450533253 / 1000000000000000000)) * (126 / 100) +
      2 * (((1450533253 / 1000000000000000000)) ^ 2 + 2 * ((2173950439 / 500000000000000000)) * ((348636203 / 1000000000000000000))) +
      6 * ((1450533253 / 1000000000000000000)) * ((348636203 / 1000000000000000000)) * (126 / 100) + 8 * ((348636203 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12970 164) (d.f1 12970 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12970 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12970 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12970 164) (d.f1 12970 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12970 164) (d.w1 12970 164) (d.w2 12970 164)
  have hwexpr0 : 0 ≤ d.w0 12970 164 + d.w1 12970 164 * √(π / 2) +
      2 * d.w2 12970 164 + energyR16 12970 *
      radiusPolynomialRoot16 (d.w0 12970 164) (d.w1 12970 164) (d.w2 12970 164) := by
    positivity
  constructor
  · change (12970 : ℝ) ^ 8 * (mA 12970 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12970 164) (d.f1 12970 164) d.f2 + locationR16 12970 *
        radiusPolynomialRoot16 (d.f0 12970 164) (d.f1 12970 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12970 : ℝ) ^ 8 * (mA 12970 : ℝ) ^ 8 *
        ((((2173950439 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2173950439 / 500000000000000000)) * ((1450533253 / 1000000000000000000)) * (126 / 100) +
          2 * (((1450533253 / 1000000000000000000)) ^ 2 + 2 * ((2173950439 / 500000000000000000)) * ((348636203 / 1000000000000000000))) +
          6 * ((1450533253 / 1000000000000000000)) * ((348636203 / 1000000000000000000)) * (126 / 100) + 8 * ((348636203 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12970) *
          (32 * (((2173950439 / 500000000000000000) : ℝ) + (1450533253 / 1000000000000000000) + (348636203 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12970 : ℝ) ^ 16 *
      (d.w0 12970 164 + d.w1 12970 164 * √(π / 2) + 2 * d.w2 12970 164 +
        energyR16 12970 * radiusPolynomialRoot16 (d.w0 12970 164) (d.w1 12970 164)
          (d.w2 12970 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12970 : ℝ) ^ 16 *
        (((1721073781 / 100000000000000000000) : ℝ) + ((612255547 / 50000000000000000000)) * (126 / 100) + 2 * ((55925637 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12970) *
          (32 * (((1721073781 / 100000000000000000000) : ℝ) + (612255547 / 50000000000000000000) + (55925637 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12970

/-! A coarse bound on the actual paper statistics constant at dimension 12971. -/
namespace BstLean.Part266.Row12971
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12969 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12969 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12969 128 ≤ (13223 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13223 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12971) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12971 : ℕ))
    (by norm_num : (12971 : ℕ) ≤ 16384)
  have ht : paperTail256 12971 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12971 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12971 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12971 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12971 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12971 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12969 128 * √(2 / (12971 : ℝ)) *
      (√(12971 : ℝ) + paperT0 12971 + paperTail256 12971) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12971 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12971 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12971 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12969 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12969 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12971 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12971

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12971
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12971 (61 / 100) 164 (17 / (100 * 12971)) (26 / (10 * 12971)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12971 (61 / 100) 164 (17 / (100 * 12971)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (447297437 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (275875379 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (215854641 / 50000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12971 / 12971 * (61 / 100)) ^ 4 * inverseRadius8 (12971 - 1) /
            envelopeGap 12971 (61 / 100) 164 (17 / (100 * 12971)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12971

namespace BstLean.Part266.Row12971
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12971 164 ≤ (1086765233 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12971 164 ≤ (90640827 / 62500000000000000)
  f2 : (tableEnvelope C).f2 ≤ (174284477 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12971 164 ≤ (1720675339 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12971 164 ≤ (1224227701 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12971 164 ≤ (447301619 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (447297437 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (447297437 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (275875379 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (215854641 / 50000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3620243 / 1000000000) : ℝ) ≤ √(17 / (100 * 12971) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12971) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2114940749 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (580311931 / 15625000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12971) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12971) ≤ (109028877 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12971) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12971 * (164 : ℝ) ^ 2 + 26 / (10 * 12971) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12971) : ℝ)) (tA 12971 * 164 ^ 2 + 26 / (10 * 12971)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3620243 / 1000000000))) * ((447297437 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3620243 / 1000000000)) ^ 3) * ((275875379 / 200000000000000000000000))) + ((215854641 / 50000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3620243 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12971) : ℝ)) d.D d.V d.P (√(tA 12971) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3620243 / 1000000000)) ^ 2 * (((2114940749 / 1000000000000000)) * ((580311931 / 15625000000000000)))) + ((215854641 / 50000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12971) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3620243 / 1000000000)) * ((447297437 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12971) : ℝ)) (tA 12971 * 164 ^ 2 + 26 / (10 * 12971)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((447297437 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3620243 / 1000000000)) ^ 2) * ((275875379 / 200000000000000000000000)) + ((215854641 / 50000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12971) : ℝ)) (√(26 / (10 * 12971) : ℝ)) d.D d.V d.P (√(tA 12971) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3620243 / 1000000000)) * (((2114940749 / 1000000000000000)) * ((580311931 / 15625000000000000))) + ((215854641 / 50000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12971) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((447297437 / 100000000000000000000) : ℝ) + ((215854641 / 50000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12971

namespace BstLean.Part266.Row12971
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12971 164 ∧
    0 ≤ (tableEnvelope C).f1 12971 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12971 164 ∧
    0 ≤ (tableEnvelope C).w1 12971 164 ∧ 0 ≤ (tableEnvelope C).w2 12971 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12971 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12971 164 ∧ 0 ≤ d.f1 12971 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12971 164 ∧ 0 ≤ d.w1 12971 164 ∧ 0 ≤ d.w2 12971 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12971 ≤ 2 * (228 / 100 : ℝ) / 12971 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12971 ≤ 2 * (370 / 100 : ℝ) / 12971 := by
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
    (completeRAData (tableEnvelope C) 12971 164).locationBound 12971 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12971 164).energyBound 12971 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12971 164) (d.f1 12971 164) d.f2 ≤
      32 * (((1086765233 / 250000000000000000) : ℝ) + (90640827 / 62500000000000000) + (174284477 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12971 164) (d.w1 12971 164)
      (d.w2 12971 164) ≤
      32 * (((1720675339 / 100000000000000000000) : ℝ) + (1224227701 / 100000000000000000000) + (447301619 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12971 164) (d.f1 12971 164) d.f2 ≤
      ((1086765233 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1086765233 / 250000000000000000)) * ((90640827 / 62500000000000000)) * (126 / 100) +
      2 * (((90640827 / 62500000000000000)) ^ 2 + 2 * ((1086765233 / 250000000000000000)) * ((174284477 / 500000000000000000))) +
      6 * ((90640827 / 62500000000000000)) * ((174284477 / 500000000000000000)) * (126 / 100) + 8 * ((174284477 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12971 164) (d.f1 12971 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12971 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12971 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12971 164) (d.f1 12971 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12971 164) (d.w1 12971 164) (d.w2 12971 164)
  have hwexpr0 : 0 ≤ d.w0 12971 164 + d.w1 12971 164 * √(π / 2) +
      2 * d.w2 12971 164 + energyR16 12971 *
      radiusPolynomialRoot16 (d.w0 12971 164) (d.w1 12971 164) (d.w2 12971 164) := by
    positivity
  constructor
  · change (12971 : ℝ) ^ 8 * (mA 12971 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12971 164) (d.f1 12971 164) d.f2 + locationR16 12971 *
        radiusPolynomialRoot16 (d.f0 12971 164) (d.f1 12971 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12971 : ℝ) ^ 8 * (mA 12971 : ℝ) ^ 8 *
        ((((1086765233 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1086765233 / 250000000000000000)) * ((90640827 / 62500000000000000)) * (126 / 100) +
          2 * (((90640827 / 62500000000000000)) ^ 2 + 2 * ((1086765233 / 250000000000000000)) * ((174284477 / 500000000000000000))) +
          6 * ((90640827 / 62500000000000000)) * ((174284477 / 500000000000000000)) * (126 / 100) + 8 * ((174284477 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12971) *
          (32 * (((1086765233 / 250000000000000000) : ℝ) + (90640827 / 62500000000000000) + (174284477 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12971 : ℝ) ^ 16 *
      (d.w0 12971 164 + d.w1 12971 164 * √(π / 2) + 2 * d.w2 12971 164 +
        energyR16 12971 * radiusPolynomialRoot16 (d.w0 12971 164) (d.w1 12971 164)
          (d.w2 12971 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12971 : ℝ) ^ 16 *
        (((1720675339 / 100000000000000000000) : ℝ) + ((1224227701 / 100000000000000000000)) * (126 / 100) + 2 * ((447301619 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12971) *
          (32 * (((1720675339 / 100000000000000000000) : ℝ) + (1224227701 / 100000000000000000000) + (447301619 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12971

/-! A coarse bound on the actual paper statistics constant at dimension 12972. -/
namespace BstLean.Part266.Row12972
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12970 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12970 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12970 128 ≤ (13224 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13224 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12972) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12972 : ℕ))
    (by norm_num : (12972 : ℕ) ≤ 16384)
  have ht : paperTail256 12972 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12972 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12972 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12972 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12972 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12972 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12970 128 * √(2 / (12972 : ℝ)) *
      (√(12972 : ℝ) + paperT0 12972 + paperTail256 12972) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12972 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12972 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12972 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12970 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12970 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12972 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12972

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12972
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12972 (61 / 100) 164 (17 / (100 * 12972)) (26 / (10 * 12972)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12972 (61 / 100) 164 (17 / (100 * 12972)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (223596997 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (344737897 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2157202989 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12972 / 12972 * (61 / 100)) ^ 4 * inverseRadius8 (12972 - 1) /
            envelopeGap 12972 (61 / 100) 164 (17 / (100 * 12972)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12972

namespace BstLean.Part266.Row12972
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12972 164 ≤ (4346224733 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12972 164 ≤ (14499741 / 10000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (17425091 / 50000000000000000)
  w0 : (tableEnvelope C).w0 12972 164 ≤ (860138867 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12972 164 ≤ (611972369 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12972 164 ≤ (223599087 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (223596997 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (223596997 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (344737897 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2157202989 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3620103 / 1000000000) : ℝ) ≤ √(17 / (100 * 12972) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12972) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1057348091 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3713423741 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12972) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12972) ≤ (13627559 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12972) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12972 * (164 : ℝ) ^ 2 + 26 / (10 * 12972) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12972) : ℝ)) (tA 12972 * 164 ^ 2 + 26 / (10 * 12972)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3620103 / 1000000000))) * ((223596997 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3620103 / 1000000000)) ^ 3) * ((344737897 / 250000000000000000000000))) + ((2157202989 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3620103 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12972) : ℝ)) d.D d.V d.P (√(tA 12972) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3620103 / 1000000000)) ^ 2 * (((1057348091 / 500000000000000)) * ((3713423741 / 100000000000000000)))) + ((2157202989 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12972) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3620103 / 1000000000)) * ((223596997 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12972) : ℝ)) (tA 12972 * 164 ^ 2 + 26 / (10 * 12972)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((223596997 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3620103 / 1000000000)) ^ 2) * ((344737897 / 250000000000000000000000)) + ((2157202989 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12972) : ℝ)) (√(26 / (10 * 12972) : ℝ)) d.D d.V d.P (√(tA 12972) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3620103 / 1000000000)) * (((1057348091 / 500000000000000)) * ((3713423741 / 100000000000000000))) + ((2157202989 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12972) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((223596997 / 50000000000000000000) : ℝ) + ((2157202989 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12972

namespace BstLean.Part266.Row12972
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12972 164 ∧
    0 ≤ (tableEnvelope C).f1 12972 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12972 164 ∧
    0 ≤ (tableEnvelope C).w1 12972 164 ∧ 0 ≤ (tableEnvelope C).w2 12972 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12972 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12972 164 ∧ 0 ≤ d.f1 12972 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12972 164 ∧ 0 ≤ d.w1 12972 164 ∧ 0 ≤ d.w2 12972 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12972 ≤ 2 * (228 / 100 : ℝ) / 12972 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12972 ≤ 2 * (370 / 100 : ℝ) / 12972 := by
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
    (completeRAData (tableEnvelope C) 12972 164).locationBound 12972 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12972 164).energyBound 12972 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12972 164) (d.f1 12972 164) d.f2 ≤
      32 * (((4346224733 / 1000000000000000000) : ℝ) + (14499741 / 10000000000000000) + (17425091 / 50000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12972 164) (d.w1 12972 164)
      (d.w2 12972 164) ≤
      32 * (((860138867 / 50000000000000000000) : ℝ) + (611972369 / 50000000000000000000) + (223599087 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12972 164) (d.f1 12972 164) d.f2 ≤
      ((4346224733 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4346224733 / 1000000000000000000)) * ((14499741 / 10000000000000000)) * (126 / 100) +
      2 * (((14499741 / 10000000000000000)) ^ 2 + 2 * ((4346224733 / 1000000000000000000)) * ((17425091 / 50000000000000000))) +
      6 * ((14499741 / 10000000000000000)) * ((17425091 / 50000000000000000)) * (126 / 100) + 8 * ((17425091 / 50000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12972 164) (d.f1 12972 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12972 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12972 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12972 164) (d.f1 12972 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12972 164) (d.w1 12972 164) (d.w2 12972 164)
  have hwexpr0 : 0 ≤ d.w0 12972 164 + d.w1 12972 164 * √(π / 2) +
      2 * d.w2 12972 164 + energyR16 12972 *
      radiusPolynomialRoot16 (d.w0 12972 164) (d.w1 12972 164) (d.w2 12972 164) := by
    positivity
  constructor
  · change (12972 : ℝ) ^ 8 * (mA 12972 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12972 164) (d.f1 12972 164) d.f2 + locationR16 12972 *
        radiusPolynomialRoot16 (d.f0 12972 164) (d.f1 12972 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12972 : ℝ) ^ 8 * (mA 12972 : ℝ) ^ 8 *
        ((((4346224733 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4346224733 / 1000000000000000000)) * ((14499741 / 10000000000000000)) * (126 / 100) +
          2 * (((14499741 / 10000000000000000)) ^ 2 + 2 * ((4346224733 / 1000000000000000000)) * ((17425091 / 50000000000000000))) +
          6 * ((14499741 / 10000000000000000)) * ((17425091 / 50000000000000000)) * (126 / 100) + 8 * ((17425091 / 50000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12972) *
          (32 * (((4346224733 / 1000000000000000000) : ℝ) + (14499741 / 10000000000000000) + (17425091 / 50000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12972 : ℝ) ^ 16 *
      (d.w0 12972 164 + d.w1 12972 164 * √(π / 2) + 2 * d.w2 12972 164 +
        energyR16 12972 * radiusPolynomialRoot16 (d.w0 12972 164) (d.w1 12972 164)
          (d.w2 12972 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12972 : ℝ) ^ 16 *
        (((860138867 / 50000000000000000000) : ℝ) + ((611972369 / 50000000000000000000)) * (126 / 100) + 2 * ((223599087 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12972) *
          (32 * (((860138867 / 50000000000000000000) : ℝ) + (611972369 / 50000000000000000000) + (223599087 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12972

/-! A coarse bound on the actual paper statistics constant at dimension 12973. -/
namespace BstLean.Part266.Row12973
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12971 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12971 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12971 128 ≤ (13225 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13225 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12973) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12973 : ℕ))
    (by norm_num : (12973 : ℕ) ≤ 16384)
  have ht : paperTail256 12973 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12973 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12973 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12973 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12973 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12973 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12971 128 * √(2 / (12973 : ℝ)) *
      (√(12973 : ℝ) + paperT0 12973 + paperTail256 12973) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12973 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12973 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12973 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12971 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12971 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12973 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12973

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12973
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12973 (61 / 100) 164 (17 / (100 * 12973)) (26 / (10 * 12973)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12973 (61 / 100) 164 (17 / (100 * 12973)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (447090583 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (275705289 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (215586051 / 50000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12973 / 12973 * (61 / 100)) ^ 4 * inverseRadius8 (12973 - 1) /
            envelopeGap 12973 (61 / 100) 164 (17 / (100 * 12973)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12973

namespace BstLean.Part266.Row12973
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12973 164 ≤ (4345385351 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12973 164 ≤ (724847127 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (34843461 / 100000000000000000)
  w0 : (tableEnvelope C).w0 12973 164 ≤ (1719879559 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12973 164 ≤ (122366153 / 10000000000000000000)
  w2 : (tableEnvelope C).w2 12973 164 ≤ (11177369 / 2500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (447090583 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (447090583 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (275705289 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (215586051 / 50000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((904991 / 250000000) : ℝ) ≤ √(17 / (100 * 12973) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12973) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1057225831 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18564256281 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12973) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12973) ≤ (109012069 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12973) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12973 * (164 : ℝ) ^ 2 + 26 / (10 * 12973) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12973) : ℝ)) (tA 12973 * 164 ^ 2 + 26 / (10 * 12973)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((904991 / 250000000))) * ((447090583 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((904991 / 250000000)) ^ 3) * ((275705289 / 200000000000000000000000))) + ((215586051 / 50000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((904991 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12973) : ℝ)) d.D d.V d.P (√(tA 12973) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((904991 / 250000000)) ^ 2 * (((1057225831 / 500000000000000)) * ((18564256281 / 500000000000000000)))) + ((215586051 / 50000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12973) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((904991 / 250000000)) * ((447090583 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12973) : ℝ)) (tA 12973 * 164 ^ 2 + 26 / (10 * 12973)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((447090583 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((904991 / 250000000)) ^ 2) * ((275705289 / 200000000000000000000000)) + ((215586051 / 50000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12973) : ℝ)) (√(26 / (10 * 12973) : ℝ)) d.D d.V d.P (√(tA 12973) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((904991 / 250000000)) * (((1057225831 / 500000000000000)) * ((18564256281 / 500000000000000000))) + ((215586051 / 50000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12973) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((447090583 / 100000000000000000000) : ℝ) + ((215586051 / 50000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12973

namespace BstLean.Part266.Row12973
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12973 164 ∧
    0 ≤ (tableEnvelope C).f1 12973 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12973 164 ∧
    0 ≤ (tableEnvelope C).w1 12973 164 ∧ 0 ≤ (tableEnvelope C).w2 12973 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12973 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12973 164 ∧ 0 ≤ d.f1 12973 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12973 164 ∧ 0 ≤ d.w1 12973 164 ∧ 0 ≤ d.w2 12973 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12973 ≤ 2 * (228 / 100 : ℝ) / 12973 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12973 ≤ 2 * (370 / 100 : ℝ) / 12973 := by
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
    (completeRAData (tableEnvelope C) 12973 164).locationBound 12973 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12973 164).energyBound 12973 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12973 164) (d.f1 12973 164) d.f2 ≤
      32 * (((4345385351 / 1000000000000000000) : ℝ) + (724847127 / 500000000000000000) + (34843461 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12973 164) (d.w1 12973 164)
      (d.w2 12973 164) ≤
      32 * (((1719879559 / 100000000000000000000) : ℝ) + (122366153 / 10000000000000000000) + (11177369 / 2500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12973 164) (d.f1 12973 164) d.f2 ≤
      ((4345385351 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4345385351 / 1000000000000000000)) * ((724847127 / 500000000000000000)) * (126 / 100) +
      2 * (((724847127 / 500000000000000000)) ^ 2 + 2 * ((4345385351 / 1000000000000000000)) * ((34843461 / 100000000000000000))) +
      6 * ((724847127 / 500000000000000000)) * ((34843461 / 100000000000000000)) * (126 / 100) + 8 * ((34843461 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12973 164) (d.f1 12973 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12973 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12973 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12973 164) (d.f1 12973 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12973 164) (d.w1 12973 164) (d.w2 12973 164)
  have hwexpr0 : 0 ≤ d.w0 12973 164 + d.w1 12973 164 * √(π / 2) +
      2 * d.w2 12973 164 + energyR16 12973 *
      radiusPolynomialRoot16 (d.w0 12973 164) (d.w1 12973 164) (d.w2 12973 164) := by
    positivity
  constructor
  · change (12973 : ℝ) ^ 8 * (mA 12973 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12973 164) (d.f1 12973 164) d.f2 + locationR16 12973 *
        radiusPolynomialRoot16 (d.f0 12973 164) (d.f1 12973 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12973 : ℝ) ^ 8 * (mA 12973 : ℝ) ^ 8 *
        ((((4345385351 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4345385351 / 1000000000000000000)) * ((724847127 / 500000000000000000)) * (126 / 100) +
          2 * (((724847127 / 500000000000000000)) ^ 2 + 2 * ((4345385351 / 1000000000000000000)) * ((34843461 / 100000000000000000))) +
          6 * ((724847127 / 500000000000000000)) * ((34843461 / 100000000000000000)) * (126 / 100) + 8 * ((34843461 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12973) *
          (32 * (((4345385351 / 1000000000000000000) : ℝ) + (724847127 / 500000000000000000) + (34843461 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12973 : ℝ) ^ 16 *
      (d.w0 12973 164 + d.w1 12973 164 * √(π / 2) + 2 * d.w2 12973 164 +
        energyR16 12973 * radiusPolynomialRoot16 (d.w0 12973 164) (d.w1 12973 164)
          (d.w2 12973 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12973 : ℝ) ^ 16 *
        (((1719879559 / 100000000000000000000) : ℝ) + ((122366153 / 10000000000000000000)) * (126 / 100) + 2 * ((11177369 / 2500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12973) *
          (32 * (((1719879559 / 100000000000000000000) : ℝ) + (122366153 / 10000000000000000000) + (11177369 / 2500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12973

/-! A coarse bound on the actual paper statistics constant at dimension 12974. -/
namespace BstLean.Part266.Row12974
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12972 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12972 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12972 128 ≤ (13226 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13226 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12974) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12974 : ℕ))
    (by norm_num : (12974 : ℕ) ≤ 16384)
  have ht : paperTail256 12974 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12974 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12974 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12974 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12974 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12974 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12972 128 * √(2 / (12974 : ℝ)) *
      (√(12974 : ℝ) + paperT0 12974 + paperTail256 12974) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12974 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12974 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12974 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12972 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12972 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12974 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12974

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12974
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12974 (61 / 100) 164 (17 / (100 * 12974)) (26 / (10 * 12974)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12974 (61 / 100) 164 (17 / (100 * 12974)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (111746801 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (689050733 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2154518971 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12974 / 12974 * (61 / 100)) ^ 4 * inverseRadius8 (12974 - 1) /
            envelopeGap 12974 (61 / 100) 164 (17 / (100 * 12974)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12974

namespace BstLean.Part266.Row12974
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12974 164 ≤ (1086137429 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12974 164 ≤ (724707649 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (87091879 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12974 164 ≤ (859741111 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12974 164 ≤ (1223378753 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12974 164 ≤ (446991379 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (111746801 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (111746801 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (689050733 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2154518971 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((226239 / 62500000) : ℝ) ≤ √(17 / (100 * 12974) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12974) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (211420719 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37122789039 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12974) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12974) ≤ (54501833 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12974) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12974 * (164 : ℝ) ^ 2 + 26 / (10 * 12974) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12974) : ℝ)) (tA 12974 * 164 ^ 2 + 26 / (10 * 12974)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((226239 / 62500000))) * ((111746801 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((226239 / 62500000)) ^ 3) * ((689050733 / 500000000000000000000000))) + ((2154518971 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((226239 / 62500000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12974) : ℝ)) d.D d.V d.P (√(tA 12974) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((226239 / 62500000)) ^ 2 * (((211420719 / 100000000000000)) * ((37122789039 / 1000000000000000000)))) + ((2154518971 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12974) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((226239 / 62500000)) * ((111746801 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12974) : ℝ)) (tA 12974 * 164 ^ 2 + 26 / (10 * 12974)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((111746801 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((226239 / 62500000)) ^ 2) * ((689050733 / 500000000000000000000000)) + ((2154518971 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12974) : ℝ)) (√(26 / (10 * 12974) : ℝ)) d.D d.V d.P (√(tA 12974) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((226239 / 62500000)) * (((211420719 / 100000000000000)) * ((37122789039 / 1000000000000000000))) + ((2154518971 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12974) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((111746801 / 25000000000000000000) : ℝ) + ((2154518971 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12974

namespace BstLean.Part266.Row12974
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12974 164 ∧
    0 ≤ (tableEnvelope C).f1 12974 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12974 164 ∧
    0 ≤ (tableEnvelope C).w1 12974 164 ∧ 0 ≤ (tableEnvelope C).w2 12974 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12974 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12974 164 ∧ 0 ≤ d.f1 12974 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12974 164 ∧ 0 ≤ d.w1 12974 164 ∧ 0 ≤ d.w2 12974 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12974 ≤ 2 * (228 / 100 : ℝ) / 12974 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12974 ≤ 2 * (370 / 100 : ℝ) / 12974 := by
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
    (completeRAData (tableEnvelope C) 12974 164).locationBound 12974 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12974 164).energyBound 12974 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12974 164) (d.f1 12974 164) d.f2 ≤
      32 * (((1086137429 / 250000000000000000) : ℝ) + (724707649 / 500000000000000000) + (87091879 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12974 164) (d.w1 12974 164)
      (d.w2 12974 164) ≤
      32 * (((859741111 / 50000000000000000000) : ℝ) + (1223378753 / 100000000000000000000) + (446991379 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12974 164) (d.f1 12974 164) d.f2 ≤
      ((1086137429 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1086137429 / 250000000000000000)) * ((724707649 / 500000000000000000)) * (126 / 100) +
      2 * (((724707649 / 500000000000000000)) ^ 2 + 2 * ((1086137429 / 250000000000000000)) * ((87091879 / 250000000000000000))) +
      6 * ((724707649 / 500000000000000000)) * ((87091879 / 250000000000000000)) * (126 / 100) + 8 * ((87091879 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12974 164) (d.f1 12974 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12974 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12974 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12974 164) (d.f1 12974 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12974 164) (d.w1 12974 164) (d.w2 12974 164)
  have hwexpr0 : 0 ≤ d.w0 12974 164 + d.w1 12974 164 * √(π / 2) +
      2 * d.w2 12974 164 + energyR16 12974 *
      radiusPolynomialRoot16 (d.w0 12974 164) (d.w1 12974 164) (d.w2 12974 164) := by
    positivity
  constructor
  · change (12974 : ℝ) ^ 8 * (mA 12974 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12974 164) (d.f1 12974 164) d.f2 + locationR16 12974 *
        radiusPolynomialRoot16 (d.f0 12974 164) (d.f1 12974 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12974 : ℝ) ^ 8 * (mA 12974 : ℝ) ^ 8 *
        ((((1086137429 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1086137429 / 250000000000000000)) * ((724707649 / 500000000000000000)) * (126 / 100) +
          2 * (((724707649 / 500000000000000000)) ^ 2 + 2 * ((1086137429 / 250000000000000000)) * ((87091879 / 250000000000000000))) +
          6 * ((724707649 / 500000000000000000)) * ((87091879 / 250000000000000000)) * (126 / 100) + 8 * ((87091879 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12974) *
          (32 * (((1086137429 / 250000000000000000) : ℝ) + (724707649 / 500000000000000000) + (87091879 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12974 : ℝ) ^ 16 *
      (d.w0 12974 164 + d.w1 12974 164 * √(π / 2) + 2 * d.w2 12974 164 +
        energyR16 12974 * radiusPolynomialRoot16 (d.w0 12974 164) (d.w1 12974 164)
          (d.w2 12974 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12974 : ℝ) ^ 16 *
        (((859741111 / 50000000000000000000) : ℝ) + ((1223378753 / 100000000000000000000)) * (126 / 100) + 2 * ((446991379 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12974) *
          (32 * (((859741111 / 50000000000000000000) : ℝ) + (1223378753 / 100000000000000000000) + (446991379 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12974
