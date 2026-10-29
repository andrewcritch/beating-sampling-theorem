import BstLean.Part266Shard30Step4


/-! A coarse bound on the actual paper statistics constant at dimension 13100. -/
namespace BstLean.Part266.Row13100
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13098 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13098 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13098 128 ≤ (13352 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13352 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13100) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13100 : ℕ))
    (by norm_num : (13100 : ℕ) ≤ 16384)
  have ht : paperTail256 13100 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13100 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13100 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13100 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13100 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13100 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13098 128 * √(2 / (13100 : ℝ)) *
      (√(13100 : ℝ) + paperT0 13100 + paperTail256 13100) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13100 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13100 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13100 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13098 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13098 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13100 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13100

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13100
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13100 (61 / 100) 165 (17 / (100 * 13100)) (26 / (10 * 13100)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13100 (61 / 100) 165 (17 / (100 * 13100)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (434212419 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (662919733 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3987300123 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13100 / 13100 * (61 / 100)) ^ 4 * inverseRadius8 (13100 - 1) /
            envelopeGap 13100 (61 / 100) 165 (17 / (100 * 13100)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13100

namespace BstLean.Part266.Row13100
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13100 165 ≤ (4240826347 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13100 165 ≤ (707405771 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (340050531 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13100 165 ≤ (835169769 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13100 165 ≤ (1188414733 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13100 165 ≤ (217108141 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (434212419 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (434212419 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (662919733 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3987300123 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1801187 / 500000000) : ℝ) ≤ √(17 / (100 * 13100) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13100) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1041888213 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36412078573 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13100) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13100) ≤ (53977617 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13100) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13100 * (165 : ℝ) ^ 2 + 26 / (10 * 13100) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13100) : ℝ)) (tA 13100 * 165 ^ 2 + 26 / (10 * 13100)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1801187 / 500000000))) * ((434212419 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1801187 / 500000000)) ^ 3) * ((662919733 / 500000000000000000000000))) + ((3987300123 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1801187 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13100) : ℝ)) d.D d.V d.P (√(tA 13100) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1801187 / 500000000)) ^ 2 * (((1041888213 / 500000000000000)) * ((36412078573 / 1000000000000000000)))) + ((3987300123 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13100) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1801187 / 500000000)) * ((434212419 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13100) : ℝ)) (tA 13100 * 165 ^ 2 + 26 / (10 * 13100)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((434212419 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1801187 / 500000000)) ^ 2) * ((662919733 / 500000000000000000000000)) + ((3987300123 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13100) : ℝ)) (√(26 / (10 * 13100) : ℝ)) d.D d.V d.P (√(tA 13100) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1801187 / 500000000)) * (((1041888213 / 500000000000000)) * ((36412078573 / 1000000000000000000))) + ((3987300123 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13100) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((434212419 / 100000000000000000000) : ℝ) + ((3987300123 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13100

namespace BstLean.Part266.Row13100
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13100 165 ∧
    0 ≤ (tableEnvelope C).f1 13100 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13100 165 ∧
    0 ≤ (tableEnvelope C).w1 13100 165 ∧ 0 ≤ (tableEnvelope C).w2 13100 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13100 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13100 165 ∧ 0 ≤ d.f1 13100 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13100 165 ∧ 0 ≤ d.w1 13100 165 ∧ 0 ≤ d.w2 13100 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13100 ≤ 2 * (228 / 100 : ℝ) / 13100 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13100 ≤ 2 * (370 / 100 : ℝ) / 13100 := by
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
    (completeRAData (tableEnvelope C) 13100 165).locationBound 13100 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13100 165).energyBound 13100 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13100 165) (d.f1 13100 165) d.f2 ≤
      32 * (((4240826347 / 1000000000000000000) : ℝ) + (707405771 / 500000000000000000) + (340050531 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13100 165) (d.w1 13100 165)
      (d.w2 13100 165) ≤
      32 * (((835169769 / 50000000000000000000) : ℝ) + (1188414733 / 100000000000000000000) + (217108141 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13100 165) (d.f1 13100 165) d.f2 ≤
      ((4240826347 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4240826347 / 1000000000000000000)) * ((707405771 / 500000000000000000)) * (126 / 100) +
      2 * (((707405771 / 500000000000000000)) ^ 2 + 2 * ((4240826347 / 1000000000000000000)) * ((340050531 / 1000000000000000000))) +
      6 * ((707405771 / 500000000000000000)) * ((340050531 / 1000000000000000000)) * (126 / 100) + 8 * ((340050531 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13100 165) (d.f1 13100 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13100 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13100 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13100 165) (d.f1 13100 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13100 165) (d.w1 13100 165) (d.w2 13100 165)
  have hwexpr0 : 0 ≤ d.w0 13100 165 + d.w1 13100 165 * √(π / 2) +
      2 * d.w2 13100 165 + energyR16 13100 *
      radiusPolynomialRoot16 (d.w0 13100 165) (d.w1 13100 165) (d.w2 13100 165) := by
    positivity
  constructor
  · change (13100 : ℝ) ^ 8 * (mA 13100 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13100 165) (d.f1 13100 165) d.f2 + locationR16 13100 *
        radiusPolynomialRoot16 (d.f0 13100 165) (d.f1 13100 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13100 : ℝ) ^ 8 * (mA 13100 : ℝ) ^ 8 *
        ((((4240826347 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4240826347 / 1000000000000000000)) * ((707405771 / 500000000000000000)) * (126 / 100) +
          2 * (((707405771 / 500000000000000000)) ^ 2 + 2 * ((4240826347 / 1000000000000000000)) * ((340050531 / 1000000000000000000))) +
          6 * ((707405771 / 500000000000000000)) * ((340050531 / 1000000000000000000)) * (126 / 100) + 8 * ((340050531 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13100) *
          (32 * (((4240826347 / 1000000000000000000) : ℝ) + (707405771 / 500000000000000000) + (340050531 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13100 : ℝ) ^ 16 *
      (d.w0 13100 165 + d.w1 13100 165 * √(π / 2) + 2 * d.w2 13100 165 +
        energyR16 13100 * radiusPolynomialRoot16 (d.w0 13100 165) (d.w1 13100 165)
          (d.w2 13100 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13100 : ℝ) ^ 16 *
        (((835169769 / 50000000000000000000) : ℝ) + ((1188414733 / 100000000000000000000)) * (126 / 100) + 2 * ((217108141 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13100) *
          (32 * (((835169769 / 50000000000000000000) : ℝ) + (1188414733 / 100000000000000000000) + (217108141 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13100

/-! A coarse bound on the actual paper statistics constant at dimension 13101. -/
namespace BstLean.Part266.Row13101
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13099 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13099 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13099 128 ≤ (13353 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13353 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13101) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13101 : ℕ))
    (by norm_num : (13101 : ℕ) ≤ 16384)
  have ht : paperTail256 13101 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13101 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13101 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13101 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13101 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13101 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13099 128 * √(2 / (13101 : ℝ)) *
      (√(13101 : ℝ) + paperT0 13101 + paperTail256 13101) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13101 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13101 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13101 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13099 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13099 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13101 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13101

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13101
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13101 (61 / 100) 165 (17 / (100 * 13101)) (26 / (10 * 13101)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13101 (61 / 100) 165 (17 / (100 * 13101)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (434112991 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1325434691 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (199242157 / 50000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13101 / 13101 * (61 / 100)) ^ 4 * inverseRadius8 (13101 - 1) /
            envelopeGap 13101 (61 / 100) 165 (17 / (100 * 13101)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13101

namespace BstLean.Part266.Row13101
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13101 165 ≤ (4240018829 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13101 165 ≤ (707270981 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (339985689 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13101 165 ≤ (1669957407 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13101 165 ≤ (1188142773 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13101 165 ≤ (108529213 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (434112991 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (434112991 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1325434691 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (199242157 / 50000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((900559 / 250000000) : ℝ) ≤ √(17 / (100 * 13101) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13101) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (520884459 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36406519897 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13101) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13101) ≤ (53973497 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13101) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13101 * (165 : ℝ) ^ 2 + 26 / (10 * 13101) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13101) : ℝ)) (tA 13101 * 165 ^ 2 + 26 / (10 * 13101)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((900559 / 250000000))) * ((434112991 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((900559 / 250000000)) ^ 3) * ((1325434691 / 1000000000000000000000000))) + ((199242157 / 50000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((900559 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13101) : ℝ)) d.D d.V d.P (√(tA 13101) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((900559 / 250000000)) ^ 2 * (((520884459 / 250000000000000)) * ((36406519897 / 1000000000000000000)))) + ((199242157 / 50000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13101) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((900559 / 250000000)) * ((434112991 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13101) : ℝ)) (tA 13101 * 165 ^ 2 + 26 / (10 * 13101)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((434112991 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((900559 / 250000000)) ^ 2) * ((1325434691 / 1000000000000000000000000)) + ((199242157 / 50000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13101) : ℝ)) (√(26 / (10 * 13101) : ℝ)) d.D d.V d.P (√(tA 13101) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((900559 / 250000000)) * (((520884459 / 250000000000000)) * ((36406519897 / 1000000000000000000))) + ((199242157 / 50000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13101) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((434112991 / 100000000000000000000) : ℝ) + ((199242157 / 50000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13101

namespace BstLean.Part266.Row13101
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13101 165 ∧
    0 ≤ (tableEnvelope C).f1 13101 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13101 165 ∧
    0 ≤ (tableEnvelope C).w1 13101 165 ∧ 0 ≤ (tableEnvelope C).w2 13101 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13101 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13101 165 ∧ 0 ≤ d.f1 13101 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13101 165 ∧ 0 ≤ d.w1 13101 165 ∧ 0 ≤ d.w2 13101 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13101 ≤ 2 * (228 / 100 : ℝ) / 13101 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13101 ≤ 2 * (370 / 100 : ℝ) / 13101 := by
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
    (completeRAData (tableEnvelope C) 13101 165).locationBound 13101 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13101 165).energyBound 13101 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13101 165) (d.f1 13101 165) d.f2 ≤
      32 * (((4240018829 / 1000000000000000000) : ℝ) + (707270981 / 500000000000000000) + (339985689 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13101 165) (d.w1 13101 165)
      (d.w2 13101 165) ≤
      32 * (((1669957407 / 100000000000000000000) : ℝ) + (1188142773 / 100000000000000000000) + (108529213 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13101 165) (d.f1 13101 165) d.f2 ≤
      ((4240018829 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4240018829 / 1000000000000000000)) * ((707270981 / 500000000000000000)) * (126 / 100) +
      2 * (((707270981 / 500000000000000000)) ^ 2 + 2 * ((4240018829 / 1000000000000000000)) * ((339985689 / 1000000000000000000))) +
      6 * ((707270981 / 500000000000000000)) * ((339985689 / 1000000000000000000)) * (126 / 100) + 8 * ((339985689 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13101 165) (d.f1 13101 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13101 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13101 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13101 165) (d.f1 13101 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13101 165) (d.w1 13101 165) (d.w2 13101 165)
  have hwexpr0 : 0 ≤ d.w0 13101 165 + d.w1 13101 165 * √(π / 2) +
      2 * d.w2 13101 165 + energyR16 13101 *
      radiusPolynomialRoot16 (d.w0 13101 165) (d.w1 13101 165) (d.w2 13101 165) := by
    positivity
  constructor
  · change (13101 : ℝ) ^ 8 * (mA 13101 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13101 165) (d.f1 13101 165) d.f2 + locationR16 13101 *
        radiusPolynomialRoot16 (d.f0 13101 165) (d.f1 13101 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13101 : ℝ) ^ 8 * (mA 13101 : ℝ) ^ 8 *
        ((((4240018829 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4240018829 / 1000000000000000000)) * ((707270981 / 500000000000000000)) * (126 / 100) +
          2 * (((707270981 / 500000000000000000)) ^ 2 + 2 * ((4240018829 / 1000000000000000000)) * ((339985689 / 1000000000000000000))) +
          6 * ((707270981 / 500000000000000000)) * ((339985689 / 1000000000000000000)) * (126 / 100) + 8 * ((339985689 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13101) *
          (32 * (((4240018829 / 1000000000000000000) : ℝ) + (707270981 / 500000000000000000) + (339985689 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13101 : ℝ) ^ 16 *
      (d.w0 13101 165 + d.w1 13101 165 * √(π / 2) + 2 * d.w2 13101 165 +
        energyR16 13101 * radiusPolynomialRoot16 (d.w0 13101 165) (d.w1 13101 165)
          (d.w2 13101 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13101 : ℝ) ^ 16 *
        (((1669957407 / 100000000000000000000) : ℝ) + ((1188142773 / 100000000000000000000)) * (126 / 100) + 2 * ((108529213 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13101) *
          (32 * (((1669957407 / 100000000000000000000) : ℝ) + (1188142773 / 100000000000000000000) + (108529213 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13101

/-! A coarse bound on the actual paper statistics constant at dimension 13102. -/
namespace BstLean.Part266.Row13102
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13100 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13100 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13100 128 ≤ (13354 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13354 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13102) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13102 : ℕ))
    (by norm_num : (13102 : ℕ) ≤ 16384)
  have ht : paperTail256 13102 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13102 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13102 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13102 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13102 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13102 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13100 128 * √(2 / (13102 : ℝ)) *
      (√(13102 : ℝ) + paperT0 13102 + paperTail256 13102) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13102 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13102 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13102 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13100 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13100 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13102 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13102

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13102
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13102 (61 / 100) 165 (17 / (100 * 13102)) (26 / (10 * 13102)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13102 (61 / 100) 165 (17 / (100 * 13102)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (217006797 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1325030071 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3982387863 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13102 / 13102 * (61 / 100)) ^ 4 * inverseRadius8 (13102 - 1) /
            envelopeGap 13102 (61 / 100) 165 (17 / (100 * 13102)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13102

namespace BstLean.Part266.Row13102
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13102 165 ≤ (529901023 / 125000000000000000)
  f1 : (tableEnvelope C).f1 13102 165 ≤ (1414271681 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (339920771 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13102 165 ≤ (1669574719 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13102 165 ≤ (296967643 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 13102 165 ≤ (108504363 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (217006797 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (217006797 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1325030071 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3982387863 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3602099 / 1000000000) : ℝ) ≤ √(17 / (100 * 13102) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13102) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (520824823 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18200481251 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13102) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13102) ≤ (21587751 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13102) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13102 * (165 : ℝ) ^ 2 + 26 / (10 * 13102) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13102) : ℝ)) (tA 13102 * 165 ^ 2 + 26 / (10 * 13102)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3602099 / 1000000000))) * ((217006797 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3602099 / 1000000000)) ^ 3) * ((1325030071 / 1000000000000000000000000))) + ((3982387863 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3602099 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13102) : ℝ)) d.D d.V d.P (√(tA 13102) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3602099 / 1000000000)) ^ 2 * (((520824823 / 250000000000000)) * ((18200481251 / 500000000000000000)))) + ((3982387863 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13102) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3602099 / 1000000000)) * ((217006797 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13102) : ℝ)) (tA 13102 * 165 ^ 2 + 26 / (10 * 13102)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((217006797 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3602099 / 1000000000)) ^ 2) * ((1325030071 / 1000000000000000000000000)) + ((3982387863 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13102) : ℝ)) (√(26 / (10 * 13102) : ℝ)) d.D d.V d.P (√(tA 13102) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3602099 / 1000000000)) * (((520824823 / 250000000000000)) * ((18200481251 / 500000000000000000))) + ((3982387863 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13102) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((217006797 / 50000000000000000000) : ℝ) + ((3982387863 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13102

namespace BstLean.Part266.Row13102
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13102 165 ∧
    0 ≤ (tableEnvelope C).f1 13102 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13102 165 ∧
    0 ≤ (tableEnvelope C).w1 13102 165 ∧ 0 ≤ (tableEnvelope C).w2 13102 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13102 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13102 165 ∧ 0 ≤ d.f1 13102 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13102 165 ∧ 0 ≤ d.w1 13102 165 ∧ 0 ≤ d.w2 13102 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13102 ≤ 2 * (228 / 100 : ℝ) / 13102 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13102 ≤ 2 * (370 / 100 : ℝ) / 13102 := by
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
    (completeRAData (tableEnvelope C) 13102 165).locationBound 13102 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13102 165).energyBound 13102 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13102 165) (d.f1 13102 165) d.f2 ≤
      32 * (((529901023 / 125000000000000000) : ℝ) + (1414271681 / 1000000000000000000) + (339920771 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13102 165) (d.w1 13102 165)
      (d.w2 13102 165) ≤
      32 * (((1669574719 / 100000000000000000000) : ℝ) + (296967643 / 25000000000000000000) + (108504363 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13102 165) (d.f1 13102 165) d.f2 ≤
      ((529901023 / 125000000000000000) : ℝ) ^ 2 + 2 * ((529901023 / 125000000000000000)) * ((1414271681 / 1000000000000000000)) * (126 / 100) +
      2 * (((1414271681 / 1000000000000000000)) ^ 2 + 2 * ((529901023 / 125000000000000000)) * ((339920771 / 1000000000000000000))) +
      6 * ((1414271681 / 1000000000000000000)) * ((339920771 / 1000000000000000000)) * (126 / 100) + 8 * ((339920771 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13102 165) (d.f1 13102 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13102 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13102 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13102 165) (d.f1 13102 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13102 165) (d.w1 13102 165) (d.w2 13102 165)
  have hwexpr0 : 0 ≤ d.w0 13102 165 + d.w1 13102 165 * √(π / 2) +
      2 * d.w2 13102 165 + energyR16 13102 *
      radiusPolynomialRoot16 (d.w0 13102 165) (d.w1 13102 165) (d.w2 13102 165) := by
    positivity
  constructor
  · change (13102 : ℝ) ^ 8 * (mA 13102 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13102 165) (d.f1 13102 165) d.f2 + locationR16 13102 *
        radiusPolynomialRoot16 (d.f0 13102 165) (d.f1 13102 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13102 : ℝ) ^ 8 * (mA 13102 : ℝ) ^ 8 *
        ((((529901023 / 125000000000000000) : ℝ) ^ 2 + 2 * ((529901023 / 125000000000000000)) * ((1414271681 / 1000000000000000000)) * (126 / 100) +
          2 * (((1414271681 / 1000000000000000000)) ^ 2 + 2 * ((529901023 / 125000000000000000)) * ((339920771 / 1000000000000000000))) +
          6 * ((1414271681 / 1000000000000000000)) * ((339920771 / 1000000000000000000)) * (126 / 100) + 8 * ((339920771 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13102) *
          (32 * (((529901023 / 125000000000000000) : ℝ) + (1414271681 / 1000000000000000000) + (339920771 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13102 : ℝ) ^ 16 *
      (d.w0 13102 165 + d.w1 13102 165 * √(π / 2) + 2 * d.w2 13102 165 +
        energyR16 13102 * radiusPolynomialRoot16 (d.w0 13102 165) (d.w1 13102 165)
          (d.w2 13102 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13102 : ℝ) ^ 16 *
        (((1669574719 / 100000000000000000000) : ℝ) + ((296967643 / 25000000000000000000)) * (126 / 100) + 2 * ((108504363 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13102) *
          (32 * (((1669574719 / 100000000000000000000) : ℝ) + (296967643 / 25000000000000000000) + (108504363 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13102

/-! A coarse bound on the actual paper statistics constant at dimension 13103. -/
namespace BstLean.Part266.Row13103
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13101 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13101 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13101 128 ≤ (13355 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13355 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13103) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13103 : ℕ))
    (by norm_num : (13103 : ℕ) ≤ 16384)
  have ht : paperTail256 13103 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13103 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13103 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13103 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13103 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13103 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13101 128 * √(2 / (13103 : ℝ)) *
      (√(13103 : ℝ) + paperT0 13103 + paperTail256 13103) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13103 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13103 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13103 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13101 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13101 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13103 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13103

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13103
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13103 (61 / 100) 165 (17 / (100 * 13103)) (26 / (10 * 13103)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13103 (61 / 100) 165 (17 / (100 * 13103)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (433914227 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (264925121 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3979934289 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13103 / 13103 * (61 / 100)) ^ 4 * inverseRadius8 (13103 - 1) /
            envelopeGap 13103 (61 / 100) 165 (17 / (100 * 13103)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13103

namespace BstLean.Part266.Row13103
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13103 165 ≤ (847680241 / 200000000000000000)
  f1 : (tableEnvelope C).f1 13103 165 ≤ (141400227 / 100000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (339855967 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13103 165 ≤ (417298211 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 13103 165 ≤ (1187598789 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13103 165 ≤ (433918083 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (433914227 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (433914227 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (264925121 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3979934289 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3601961 / 1000000000) : ℝ) ≤ √(17 / (100 * 13103) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13103) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1041530397 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36395406373 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13103) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13103) ≤ (107930517 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13103) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13103 * (165 : ℝ) ^ 2 + 26 / (10 * 13103) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13103) : ℝ)) (tA 13103 * 165 ^ 2 + 26 / (10 * 13103)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3601961 / 1000000000))) * ((433914227 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3601961 / 1000000000)) ^ 3) * ((264925121 / 200000000000000000000000))) + ((3979934289 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3601961 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13103) : ℝ)) d.D d.V d.P (√(tA 13103) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3601961 / 1000000000)) ^ 2 * (((1041530397 / 500000000000000)) * ((36395406373 / 1000000000000000000)))) + ((3979934289 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13103) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3601961 / 1000000000)) * ((433914227 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13103) : ℝ)) (tA 13103 * 165 ^ 2 + 26 / (10 * 13103)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((433914227 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3601961 / 1000000000)) ^ 2) * ((264925121 / 200000000000000000000000)) + ((3979934289 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13103) : ℝ)) (√(26 / (10 * 13103) : ℝ)) d.D d.V d.P (√(tA 13103) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3601961 / 1000000000)) * (((1041530397 / 500000000000000)) * ((36395406373 / 1000000000000000000))) + ((3979934289 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13103) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((433914227 / 100000000000000000000) : ℝ) + ((3979934289 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13103

namespace BstLean.Part266.Row13103
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13103 165 ∧
    0 ≤ (tableEnvelope C).f1 13103 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13103 165 ∧
    0 ≤ (tableEnvelope C).w1 13103 165 ∧ 0 ≤ (tableEnvelope C).w2 13103 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13103 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13103 165 ∧ 0 ≤ d.f1 13103 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13103 165 ∧ 0 ≤ d.w1 13103 165 ∧ 0 ≤ d.w2 13103 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13103 ≤ 2 * (228 / 100 : ℝ) / 13103 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13103 ≤ 2 * (370 / 100 : ℝ) / 13103 := by
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
    (completeRAData (tableEnvelope C) 13103 165).locationBound 13103 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13103 165).energyBound 13103 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13103 165) (d.f1 13103 165) d.f2 ≤
      32 * (((847680241 / 200000000000000000) : ℝ) + (141400227 / 100000000000000000) + (339855967 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13103 165) (d.w1 13103 165)
      (d.w2 13103 165) ≤
      32 * (((417298211 / 25000000000000000000) : ℝ) + (1187598789 / 100000000000000000000) + (433918083 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13103 165) (d.f1 13103 165) d.f2 ≤
      ((847680241 / 200000000000000000) : ℝ) ^ 2 + 2 * ((847680241 / 200000000000000000)) * ((141400227 / 100000000000000000)) * (126 / 100) +
      2 * (((141400227 / 100000000000000000)) ^ 2 + 2 * ((847680241 / 200000000000000000)) * ((339855967 / 1000000000000000000))) +
      6 * ((141400227 / 100000000000000000)) * ((339855967 / 1000000000000000000)) * (126 / 100) + 8 * ((339855967 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13103 165) (d.f1 13103 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13103 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13103 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13103 165) (d.f1 13103 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13103 165) (d.w1 13103 165) (d.w2 13103 165)
  have hwexpr0 : 0 ≤ d.w0 13103 165 + d.w1 13103 165 * √(π / 2) +
      2 * d.w2 13103 165 + energyR16 13103 *
      radiusPolynomialRoot16 (d.w0 13103 165) (d.w1 13103 165) (d.w2 13103 165) := by
    positivity
  constructor
  · change (13103 : ℝ) ^ 8 * (mA 13103 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13103 165) (d.f1 13103 165) d.f2 + locationR16 13103 *
        radiusPolynomialRoot16 (d.f0 13103 165) (d.f1 13103 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13103 : ℝ) ^ 8 * (mA 13103 : ℝ) ^ 8 *
        ((((847680241 / 200000000000000000) : ℝ) ^ 2 + 2 * ((847680241 / 200000000000000000)) * ((141400227 / 100000000000000000)) * (126 / 100) +
          2 * (((141400227 / 100000000000000000)) ^ 2 + 2 * ((847680241 / 200000000000000000)) * ((339855967 / 1000000000000000000))) +
          6 * ((141400227 / 100000000000000000)) * ((339855967 / 1000000000000000000)) * (126 / 100) + 8 * ((339855967 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13103) *
          (32 * (((847680241 / 200000000000000000) : ℝ) + (141400227 / 100000000000000000) + (339855967 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13103 : ℝ) ^ 16 *
      (d.w0 13103 165 + d.w1 13103 165 * √(π / 2) + 2 * d.w2 13103 165 +
        energyR16 13103 * radiusPolynomialRoot16 (d.w0 13103 165) (d.w1 13103 165)
          (d.w2 13103 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13103 : ℝ) ^ 16 *
        (((417298211 / 25000000000000000000) : ℝ) + ((1187598789 / 100000000000000000000)) * (126 / 100) + 2 * ((433918083 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13103) *
          (32 * (((417298211 / 25000000000000000000) : ℝ) + (1187598789 / 100000000000000000000) + (433918083 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13103

/-! A coarse bound on the actual paper statistics constant at dimension 13104. -/
namespace BstLean.Part266.Row13104
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13102 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13102 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13102 128 ≤ (13356 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13356 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13104) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13104 : ℕ))
    (by norm_num : (13104 : ℕ) ≤ 16384)
  have ht : paperTail256 13104 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13104 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13104 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13104 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13104 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13104 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13102 128 * √(2 / (13104 : ℝ)) *
      (√(13104 : ℝ) + paperT0 13104 + paperTail256 13104) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13104 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13104 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13104 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13102 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13102 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13104 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13104

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13104
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13104 (61 / 100) 165 (17 / (100 * 13104)) (26 / (10 * 13104)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13104 (61 / 100) 165 (17 / (100 * 13104)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (43381489 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1324221293 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3977482417 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13104 / 13104 * (61 / 100)) ^ 4 * inverseRadius8 (13104 - 1) /
            envelopeGap 13104 (61 / 100) 165 (17 / (100 * 13104)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13104

namespace BstLean.Part266.Row13104
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13104 165 ≤ (4237591097 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13104 165 ≤ (1413732157 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (339791087 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13104 165 ≤ (1668810409 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13104 165 ≤ (296831691 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 13104 165 ≤ (433818743 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (43381489 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (43381489 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1324221293 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3977482417 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((112557 / 31250000) : ℝ) ≤ √(17 / (100 * 13104) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13104) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (104141117 / 50000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4548731439 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13104) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13104) ≤ (107922281 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13104) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13104 * (165 : ℝ) ^ 2 + 26 / (10 * 13104) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13104) : ℝ)) (tA 13104 * 165 ^ 2 + 26 / (10 * 13104)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((112557 / 31250000))) * ((43381489 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((112557 / 31250000)) ^ 3) * ((1324221293 / 1000000000000000000000000))) + ((3977482417 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((112557 / 31250000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13104) : ℝ)) d.D d.V d.P (√(tA 13104) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((112557 / 31250000)) ^ 2 * (((104141117 / 50000000000000)) * ((4548731439 / 125000000000000000)))) + ((3977482417 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13104) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((112557 / 31250000)) * ((43381489 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13104) : ℝ)) (tA 13104 * 165 ^ 2 + 26 / (10 * 13104)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((43381489 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((112557 / 31250000)) ^ 2) * ((1324221293 / 1000000000000000000000000)) + ((3977482417 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13104) : ℝ)) (√(26 / (10 * 13104) : ℝ)) d.D d.V d.P (√(tA 13104) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((112557 / 31250000)) * (((104141117 / 50000000000000)) * ((4548731439 / 125000000000000000))) + ((3977482417 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13104) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((43381489 / 10000000000000000000) : ℝ) + ((3977482417 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13104

namespace BstLean.Part266.Row13104
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13104 165 ∧
    0 ≤ (tableEnvelope C).f1 13104 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13104 165 ∧
    0 ≤ (tableEnvelope C).w1 13104 165 ∧ 0 ≤ (tableEnvelope C).w2 13104 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13104 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13104 165 ∧ 0 ≤ d.f1 13104 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13104 165 ∧ 0 ≤ d.w1 13104 165 ∧ 0 ≤ d.w2 13104 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13104 ≤ 2 * (228 / 100 : ℝ) / 13104 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13104 ≤ 2 * (370 / 100 : ℝ) / 13104 := by
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
    (completeRAData (tableEnvelope C) 13104 165).locationBound 13104 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13104 165).energyBound 13104 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13104 165) (d.f1 13104 165) d.f2 ≤
      32 * (((4237591097 / 1000000000000000000) : ℝ) + (1413732157 / 1000000000000000000) + (339791087 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13104 165) (d.w1 13104 165)
      (d.w2 13104 165) ≤
      32 * (((1668810409 / 100000000000000000000) : ℝ) + (296831691 / 25000000000000000000) + (433818743 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13104 165) (d.f1 13104 165) d.f2 ≤
      ((4237591097 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4237591097 / 1000000000000000000)) * ((1413732157 / 1000000000000000000)) * (126 / 100) +
      2 * (((1413732157 / 1000000000000000000)) ^ 2 + 2 * ((4237591097 / 1000000000000000000)) * ((339791087 / 1000000000000000000))) +
      6 * ((1413732157 / 1000000000000000000)) * ((339791087 / 1000000000000000000)) * (126 / 100) + 8 * ((339791087 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13104 165) (d.f1 13104 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13104 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13104 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13104 165) (d.f1 13104 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13104 165) (d.w1 13104 165) (d.w2 13104 165)
  have hwexpr0 : 0 ≤ d.w0 13104 165 + d.w1 13104 165 * √(π / 2) +
      2 * d.w2 13104 165 + energyR16 13104 *
      radiusPolynomialRoot16 (d.w0 13104 165) (d.w1 13104 165) (d.w2 13104 165) := by
    positivity
  constructor
  · change (13104 : ℝ) ^ 8 * (mA 13104 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13104 165) (d.f1 13104 165) d.f2 + locationR16 13104 *
        radiusPolynomialRoot16 (d.f0 13104 165) (d.f1 13104 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13104 : ℝ) ^ 8 * (mA 13104 : ℝ) ^ 8 *
        ((((4237591097 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4237591097 / 1000000000000000000)) * ((1413732157 / 1000000000000000000)) * (126 / 100) +
          2 * (((1413732157 / 1000000000000000000)) ^ 2 + 2 * ((4237591097 / 1000000000000000000)) * ((339791087 / 1000000000000000000))) +
          6 * ((1413732157 / 1000000000000000000)) * ((339791087 / 1000000000000000000)) * (126 / 100) + 8 * ((339791087 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13104) *
          (32 * (((4237591097 / 1000000000000000000) : ℝ) + (1413732157 / 1000000000000000000) + (339791087 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13104 : ℝ) ^ 16 *
      (d.w0 13104 165 + d.w1 13104 165 * √(π / 2) + 2 * d.w2 13104 165 +
        energyR16 13104 * radiusPolynomialRoot16 (d.w0 13104 165) (d.w1 13104 165)
          (d.w2 13104 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13104 : ℝ) ^ 16 *
        (((1668810409 / 100000000000000000000) : ℝ) + ((296831691 / 25000000000000000000)) * (126 / 100) + 2 * ((433818743 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13104) *
          (32 * (((1668810409 / 100000000000000000000) : ℝ) + (296831691 / 25000000000000000000) + (433818743 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13104

/-! A coarse bound on the actual paper statistics constant at dimension 13105. -/
namespace BstLean.Part266.Row13105
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13103 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13103 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13103 128 ≤ (13357 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13357 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13105) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13105 : ℕ))
    (by norm_num : (13105 : ℕ) ≤ 16384)
  have ht : paperTail256 13105 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13105 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13105 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13105 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13105 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13105 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13103 128 * √(2 / (13105 : ℝ)) *
      (√(13105 : ℝ) + paperT0 13105 + paperTail256 13105) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13105 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13105 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13105 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13103 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13103 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13105 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13105

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13105
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13105 (61 / 100) 165 (17 / (100 * 13105)) (26 / (10 * 13105)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13105 (61 / 100) 165 (17 / (100 * 13105)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (433715583 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (82738571 / 62500000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3975032247 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13105 / 13105 * (61 / 100)) ^ 4 * inverseRadius8 (13105 - 1) /
            envelopeGap 13105 (61 / 100) 165 (17 / (100 * 13105)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13105

namespace BstLean.Part266.Row13105
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13105 165 ≤ (4236784657 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13105 165 ≤ (706731457 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (4246579 / 12500000000000000)
  w0 : (tableEnvelope C).w0 13105 165 ≤ (1668428789 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13105 165 ≤ (1187055157 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13105 165 ≤ (216859717 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (433715583 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (433715583 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (82738571 / 62500000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3975032247 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1800843 / 500000000) : ℝ) ≤ √(17 / (100 * 13105) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13105) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (520645983 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9096074483 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13105) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13105) ≤ (53957023 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13105) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13105 * (165 : ℝ) ^ 2 + 26 / (10 * 13105) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13105) : ℝ)) (tA 13105 * 165 ^ 2 + 26 / (10 * 13105)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1800843 / 500000000))) * ((433715583 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1800843 / 500000000)) ^ 3) * ((82738571 / 62500000000000000000000))) + ((3975032247 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1800843 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13105) : ℝ)) d.D d.V d.P (√(tA 13105) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1800843 / 500000000)) ^ 2 * (((520645983 / 250000000000000)) * ((9096074483 / 250000000000000000)))) + ((3975032247 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13105) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1800843 / 500000000)) * ((433715583 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13105) : ℝ)) (tA 13105 * 165 ^ 2 + 26 / (10 * 13105)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((433715583 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1800843 / 500000000)) ^ 2) * ((82738571 / 62500000000000000000000)) + ((3975032247 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13105) : ℝ)) (√(26 / (10 * 13105) : ℝ)) d.D d.V d.P (√(tA 13105) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1800843 / 500000000)) * (((520645983 / 250000000000000)) * ((9096074483 / 250000000000000000))) + ((3975032247 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13105) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((433715583 / 100000000000000000000) : ℝ) + ((3975032247 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13105

namespace BstLean.Part266.Row13105
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13105 165 ∧
    0 ≤ (tableEnvelope C).f1 13105 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13105 165 ∧
    0 ≤ (tableEnvelope C).w1 13105 165 ∧ 0 ≤ (tableEnvelope C).w2 13105 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13105 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13105 165 ∧ 0 ≤ d.f1 13105 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13105 165 ∧ 0 ≤ d.w1 13105 165 ∧ 0 ≤ d.w2 13105 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13105 ≤ 2 * (228 / 100 : ℝ) / 13105 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13105 ≤ 2 * (370 / 100 : ℝ) / 13105 := by
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
    (completeRAData (tableEnvelope C) 13105 165).locationBound 13105 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13105 165).energyBound 13105 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13105 165) (d.f1 13105 165) d.f2 ≤
      32 * (((4236784657 / 1000000000000000000) : ℝ) + (706731457 / 500000000000000000) + (4246579 / 12500000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13105 165) (d.w1 13105 165)
      (d.w2 13105 165) ≤
      32 * (((1668428789 / 100000000000000000000) : ℝ) + (1187055157 / 100000000000000000000) + (216859717 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13105 165) (d.f1 13105 165) d.f2 ≤
      ((4236784657 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4236784657 / 1000000000000000000)) * ((706731457 / 500000000000000000)) * (126 / 100) +
      2 * (((706731457 / 500000000000000000)) ^ 2 + 2 * ((4236784657 / 1000000000000000000)) * ((4246579 / 12500000000000000))) +
      6 * ((706731457 / 500000000000000000)) * ((4246579 / 12500000000000000)) * (126 / 100) + 8 * ((4246579 / 12500000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13105 165) (d.f1 13105 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13105 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13105 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13105 165) (d.f1 13105 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13105 165) (d.w1 13105 165) (d.w2 13105 165)
  have hwexpr0 : 0 ≤ d.w0 13105 165 + d.w1 13105 165 * √(π / 2) +
      2 * d.w2 13105 165 + energyR16 13105 *
      radiusPolynomialRoot16 (d.w0 13105 165) (d.w1 13105 165) (d.w2 13105 165) := by
    positivity
  constructor
  · change (13105 : ℝ) ^ 8 * (mA 13105 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13105 165) (d.f1 13105 165) d.f2 + locationR16 13105 *
        radiusPolynomialRoot16 (d.f0 13105 165) (d.f1 13105 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13105 : ℝ) ^ 8 * (mA 13105 : ℝ) ^ 8 *
        ((((4236784657 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4236784657 / 1000000000000000000)) * ((706731457 / 500000000000000000)) * (126 / 100) +
          2 * (((706731457 / 500000000000000000)) ^ 2 + 2 * ((4236784657 / 1000000000000000000)) * ((4246579 / 12500000000000000))) +
          6 * ((706731457 / 500000000000000000)) * ((4246579 / 12500000000000000)) * (126 / 100) + 8 * ((4246579 / 12500000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13105) *
          (32 * (((4236784657 / 1000000000000000000) : ℝ) + (706731457 / 500000000000000000) + (4246579 / 12500000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13105 : ℝ) ^ 16 *
      (d.w0 13105 165 + d.w1 13105 165 * √(π / 2) + 2 * d.w2 13105 165 +
        energyR16 13105 * radiusPolynomialRoot16 (d.w0 13105 165) (d.w1 13105 165)
          (d.w2 13105 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13105 : ℝ) ^ 16 *
        (((1668428789 / 100000000000000000000) : ℝ) + ((1187055157 / 100000000000000000000)) * (126 / 100) + 2 * ((216859717 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13105) *
          (32 * (((1668428789 / 100000000000000000000) : ℝ) + (1187055157 / 100000000000000000000) + (216859717 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13105

/-! A coarse bound on the actual paper statistics constant at dimension 13106. -/
namespace BstLean.Part266.Row13106
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13104 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13104 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13104 128 ≤ (13358 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13358 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13106) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13106 : ℕ))
    (by norm_num : (13106 : ℕ) ≤ 16384)
  have ht : paperTail256 13106 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13106 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13106 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13106 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13106 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13106 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13104 128 * √(2 / (13106 : ℝ)) *
      (√(13106 : ℝ) + paperT0 13106 + paperTail256 13106) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13106 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13106 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13106 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13104 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13104 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13106 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13106

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13106
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13106 (61 / 100) 165 (17 / (100 * 13106)) (26 / (10 * 13106)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13106 (61 / 100) 165 (17 / (100 * 13106)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (433616307 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1323413133 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (158903351 / 40000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13106 / 13106 * (61 / 100)) ^ 4 * inverseRadius8 (13106 - 1) /
            envelopeGap 13106 (61 / 100) 165 (17 / (100 * 13106)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13106

namespace BstLean.Part266.Row13106
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13106 165 ≤ (423597509 / 100000000000000000)
  f1 : (tableEnvelope C).f1 13106 165 ≤ (1413192971 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (339661477 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13106 165 ≤ (166804661 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 13106 165 ≤ (1186783309 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13106 165 ≤ (108405039 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (433616307 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (433616307 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1323413133 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (158903351 / 40000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3601549 / 1000000000) : ℝ) ≤ √(17 / (100 * 13106) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13106) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (208234557 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18189372811 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13106) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13106) ≤ (26976453 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13106) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13106 * (165 : ℝ) ^ 2 + 26 / (10 * 13106) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13106) : ℝ)) (tA 13106 * 165 ^ 2 + 26 / (10 * 13106)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3601549 / 1000000000))) * ((433616307 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3601549 / 1000000000)) ^ 3) * ((1323413133 / 1000000000000000000000000))) + ((158903351 / 40000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3601549 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13106) : ℝ)) d.D d.V d.P (√(tA 13106) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3601549 / 1000000000)) ^ 2 * (((208234557 / 100000000000000)) * ((18189372811 / 500000000000000000)))) + ((158903351 / 40000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13106) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3601549 / 1000000000)) * ((433616307 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13106) : ℝ)) (tA 13106 * 165 ^ 2 + 26 / (10 * 13106)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((433616307 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3601549 / 1000000000)) ^ 2) * ((1323413133 / 1000000000000000000000000)) + ((158903351 / 40000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13106) : ℝ)) (√(26 / (10 * 13106) : ℝ)) d.D d.V d.P (√(tA 13106) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3601549 / 1000000000)) * (((208234557 / 100000000000000)) * ((18189372811 / 500000000000000000))) + ((158903351 / 40000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13106) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((433616307 / 100000000000000000000) : ℝ) + ((158903351 / 40000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13106

namespace BstLean.Part266.Row13106
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13106 165 ∧
    0 ≤ (tableEnvelope C).f1 13106 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13106 165 ∧
    0 ≤ (tableEnvelope C).w1 13106 165 ∧ 0 ≤ (tableEnvelope C).w2 13106 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13106 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13106 165 ∧ 0 ≤ d.f1 13106 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13106 165 ∧ 0 ≤ d.w1 13106 165 ∧ 0 ≤ d.w2 13106 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13106 ≤ 2 * (228 / 100 : ℝ) / 13106 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13106 ≤ 2 * (370 / 100 : ℝ) / 13106 := by
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
    (completeRAData (tableEnvelope C) 13106 165).locationBound 13106 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13106 165).energyBound 13106 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13106 165) (d.f1 13106 165) d.f2 ≤
      32 * (((423597509 / 100000000000000000) : ℝ) + (1413192971 / 1000000000000000000) + (339661477 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13106 165) (d.w1 13106 165)
      (d.w2 13106 165) ≤
      32 * (((166804661 / 10000000000000000000) : ℝ) + (1186783309 / 100000000000000000000) + (108405039 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13106 165) (d.f1 13106 165) d.f2 ≤
      ((423597509 / 100000000000000000) : ℝ) ^ 2 + 2 * ((423597509 / 100000000000000000)) * ((1413192971 / 1000000000000000000)) * (126 / 100) +
      2 * (((1413192971 / 1000000000000000000)) ^ 2 + 2 * ((423597509 / 100000000000000000)) * ((339661477 / 1000000000000000000))) +
      6 * ((1413192971 / 1000000000000000000)) * ((339661477 / 1000000000000000000)) * (126 / 100) + 8 * ((339661477 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13106 165) (d.f1 13106 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13106 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13106 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13106 165) (d.f1 13106 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13106 165) (d.w1 13106 165) (d.w2 13106 165)
  have hwexpr0 : 0 ≤ d.w0 13106 165 + d.w1 13106 165 * √(π / 2) +
      2 * d.w2 13106 165 + energyR16 13106 *
      radiusPolynomialRoot16 (d.w0 13106 165) (d.w1 13106 165) (d.w2 13106 165) := by
    positivity
  constructor
  · change (13106 : ℝ) ^ 8 * (mA 13106 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13106 165) (d.f1 13106 165) d.f2 + locationR16 13106 *
        radiusPolynomialRoot16 (d.f0 13106 165) (d.f1 13106 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13106 : ℝ) ^ 8 * (mA 13106 : ℝ) ^ 8 *
        ((((423597509 / 100000000000000000) : ℝ) ^ 2 + 2 * ((423597509 / 100000000000000000)) * ((1413192971 / 1000000000000000000)) * (126 / 100) +
          2 * (((1413192971 / 1000000000000000000)) ^ 2 + 2 * ((423597509 / 100000000000000000)) * ((339661477 / 1000000000000000000))) +
          6 * ((1413192971 / 1000000000000000000)) * ((339661477 / 1000000000000000000)) * (126 / 100) + 8 * ((339661477 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13106) *
          (32 * (((423597509 / 100000000000000000) : ℝ) + (1413192971 / 1000000000000000000) + (339661477 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13106 : ℝ) ^ 16 *
      (d.w0 13106 165 + d.w1 13106 165 * √(π / 2) + 2 * d.w2 13106 165 +
        energyR16 13106 * radiusPolynomialRoot16 (d.w0 13106 165) (d.w1 13106 165)
          (d.w2 13106 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13106 : ℝ) ^ 16 *
        (((166804661 / 10000000000000000000) : ℝ) + ((1186783309 / 100000000000000000000)) * (126 / 100) + 2 * ((108405039 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13106) *
          (32 * (((166804661 / 10000000000000000000) : ℝ) + (1186783309 / 100000000000000000000) + (108405039 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13106

/-! A coarse bound on the actual paper statistics constant at dimension 13107. -/
namespace BstLean.Part266.Row13107
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13105 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13105 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13105 128 ≤ (13359 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13359 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13107) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13107 : ℕ))
    (by norm_num : (13107 : ℕ) ≤ 16384)
  have ht : paperTail256 13107 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13107 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13107 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13107 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13107 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13107 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13105 128 * √(2 / (13107 : ℝ)) *
      (√(13107 : ℝ) + paperT0 13107 + paperTail256 13107) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13107 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13107 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13107 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13105 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13105 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13107 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13107

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13107
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13107 (61 / 100) 165 (17 / (100 * 13107)) (26 / (10 * 13107)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13107 (61 / 100) 165 (17 / (100 * 13107)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (433517061 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (330752321 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1985068501 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13107 / 13107 * (61 / 100)) ^ 4 * inverseRadius8 (13107 - 1) /
            envelopeGap 13107 (61 / 100) 165 (17 / (100 * 13107)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13107

namespace BstLean.Part266.Row13107
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13107 165 ≤ (4235165793 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13107 165 ≤ (176615389 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (169798327 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13107 165 ≤ (1667664559 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13107 165 ≤ (1186511549 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13107 165 ≤ (433520907 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (433517061 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (433517061 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (330752321 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1985068501 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((900353 / 250000000) : ℝ) ≤ √(17 / (100 * 13107) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13107) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2082107253 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36373194581 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13107) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13107) ≤ (107897579 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13107) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13107 * (165 : ℝ) ^ 2 + 26 / (10 * 13107) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13107) : ℝ)) (tA 13107 * 165 ^ 2 + 26 / (10 * 13107)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((900353 / 250000000))) * ((433517061 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((900353 / 250000000)) ^ 3) * ((330752321 / 250000000000000000000000))) + ((1985068501 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((900353 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13107) : ℝ)) d.D d.V d.P (√(tA 13107) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((900353 / 250000000)) ^ 2 * (((2082107253 / 1000000000000000)) * ((36373194581 / 1000000000000000000)))) + ((1985068501 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13107) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((900353 / 250000000)) * ((433517061 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13107) : ℝ)) (tA 13107 * 165 ^ 2 + 26 / (10 * 13107)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((433517061 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((900353 / 250000000)) ^ 2) * ((330752321 / 250000000000000000000000)) + ((1985068501 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13107) : ℝ)) (√(26 / (10 * 13107) : ℝ)) d.D d.V d.P (√(tA 13107) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((900353 / 250000000)) * (((2082107253 / 1000000000000000)) * ((36373194581 / 1000000000000000000))) + ((1985068501 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13107) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((433517061 / 100000000000000000000) : ℝ) + ((1985068501 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13107

namespace BstLean.Part266.Row13107
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13107 165 ∧
    0 ≤ (tableEnvelope C).f1 13107 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13107 165 ∧
    0 ≤ (tableEnvelope C).w1 13107 165 ∧ 0 ≤ (tableEnvelope C).w2 13107 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13107 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13107 165 ∧ 0 ≤ d.f1 13107 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13107 165 ∧ 0 ≤ d.w1 13107 165 ∧ 0 ≤ d.w2 13107 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13107 ≤ 2 * (228 / 100 : ℝ) / 13107 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13107 ≤ 2 * (370 / 100 : ℝ) / 13107 := by
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
    (completeRAData (tableEnvelope C) 13107 165).locationBound 13107 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13107 165).energyBound 13107 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13107 165) (d.f1 13107 165) d.f2 ≤
      32 * (((4235165793 / 1000000000000000000) : ℝ) + (176615389 / 125000000000000000) + (169798327 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13107 165) (d.w1 13107 165)
      (d.w2 13107 165) ≤
      32 * (((1667664559 / 100000000000000000000) : ℝ) + (1186511549 / 100000000000000000000) + (433520907 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13107 165) (d.f1 13107 165) d.f2 ≤
      ((4235165793 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4235165793 / 1000000000000000000)) * ((176615389 / 125000000000000000)) * (126 / 100) +
      2 * (((176615389 / 125000000000000000)) ^ 2 + 2 * ((4235165793 / 1000000000000000000)) * ((169798327 / 500000000000000000))) +
      6 * ((176615389 / 125000000000000000)) * ((169798327 / 500000000000000000)) * (126 / 100) + 8 * ((169798327 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13107 165) (d.f1 13107 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13107 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13107 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13107 165) (d.f1 13107 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13107 165) (d.w1 13107 165) (d.w2 13107 165)
  have hwexpr0 : 0 ≤ d.w0 13107 165 + d.w1 13107 165 * √(π / 2) +
      2 * d.w2 13107 165 + energyR16 13107 *
      radiusPolynomialRoot16 (d.w0 13107 165) (d.w1 13107 165) (d.w2 13107 165) := by
    positivity
  constructor
  · change (13107 : ℝ) ^ 8 * (mA 13107 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13107 165) (d.f1 13107 165) d.f2 + locationR16 13107 *
        radiusPolynomialRoot16 (d.f0 13107 165) (d.f1 13107 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13107 : ℝ) ^ 8 * (mA 13107 : ℝ) ^ 8 *
        ((((4235165793 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4235165793 / 1000000000000000000)) * ((176615389 / 125000000000000000)) * (126 / 100) +
          2 * (((176615389 / 125000000000000000)) ^ 2 + 2 * ((4235165793 / 1000000000000000000)) * ((169798327 / 500000000000000000))) +
          6 * ((176615389 / 125000000000000000)) * ((169798327 / 500000000000000000)) * (126 / 100) + 8 * ((169798327 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13107) *
          (32 * (((4235165793 / 1000000000000000000) : ℝ) + (176615389 / 125000000000000000) + (169798327 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13107 : ℝ) ^ 16 *
      (d.w0 13107 165 + d.w1 13107 165 * √(π / 2) + 2 * d.w2 13107 165 +
        energyR16 13107 * radiusPolynomialRoot16 (d.w0 13107 165) (d.w1 13107 165)
          (d.w2 13107 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13107 : ℝ) ^ 16 *
        (((1667664559 / 100000000000000000000) : ℝ) + ((1186511549 / 100000000000000000000)) * (126 / 100) + 2 * ((433520907 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13107) *
          (32 * (((1667664559 / 100000000000000000000) : ℝ) + (1186511549 / 100000000000000000000) + (433520907 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13107

/-! A coarse bound on the actual paper statistics constant at dimension 13108. -/
namespace BstLean.Part266.Row13108
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13106 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13106 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13106 128 ≤ (13360 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13360 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13108) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13108 : ℕ))
    (by norm_num : (13108 : ℕ) ≤ 16384)
  have ht : paperTail256 13108 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13108 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13108 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13108 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13108 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13108 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13106 128 * √(2 / (13108 : ℝ)) *
      (√(13108 : ℝ) + paperT0 13108 + paperTail256 13108) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13108 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13108 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13108 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13106 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13106 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13108 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13108

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13108
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13108 (61 / 100) 165 (17 / (100 * 13108)) (26 / (10 * 13108)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13108 (61 / 100) 165 (17 / (100 * 13108)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (216708923 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1322605589 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1983845963 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13108 / 13108 * (61 / 100)) ^ 4 * inverseRadius8 (13108 - 1) /
            envelopeGap 13108 (61 / 100) 165 (17 / (100 * 13108)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13108

namespace BstLean.Part266.Row13108
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13108 165 ≤ (4234360159 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13108 165 ≤ (1412654123 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (42441493 / 125000000000000000)
  w0 : (tableEnvelope C).w0 13108 165 ≤ (1667283321 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13108 165 ≤ (1186240207 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13108 165 ≤ (43342169 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (216708923 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (216708923 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1322605589 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1983845963 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1800637 / 500000000) : ℝ) ≤ √(17 / (100 * 13108) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13108) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2081868983 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3636764481 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13108) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13108) ≤ (26972337 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13108) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13108 * (165 : ℝ) ^ 2 + 26 / (10 * 13108) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13108) : ℝ)) (tA 13108 * 165 ^ 2 + 26 / (10 * 13108)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1800637 / 500000000))) * ((216708923 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1800637 / 500000000)) ^ 3) * ((1322605589 / 1000000000000000000000000))) + ((1983845963 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1800637 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13108) : ℝ)) d.D d.V d.P (√(tA 13108) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1800637 / 500000000)) ^ 2 * (((2081868983 / 1000000000000000)) * ((3636764481 / 100000000000000000)))) + ((1983845963 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13108) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1800637 / 500000000)) * ((216708923 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13108) : ℝ)) (tA 13108 * 165 ^ 2 + 26 / (10 * 13108)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((216708923 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1800637 / 500000000)) ^ 2) * ((1322605589 / 1000000000000000000000000)) + ((1983845963 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13108) : ℝ)) (√(26 / (10 * 13108) : ℝ)) d.D d.V d.P (√(tA 13108) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1800637 / 500000000)) * (((2081868983 / 1000000000000000)) * ((3636764481 / 100000000000000000))) + ((1983845963 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13108) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((216708923 / 50000000000000000000) : ℝ) + ((1983845963 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13108

namespace BstLean.Part266.Row13108
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13108 165 ∧
    0 ≤ (tableEnvelope C).f1 13108 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13108 165 ∧
    0 ≤ (tableEnvelope C).w1 13108 165 ∧ 0 ≤ (tableEnvelope C).w2 13108 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13108 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13108 165 ∧ 0 ≤ d.f1 13108 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13108 165 ∧ 0 ≤ d.w1 13108 165 ∧ 0 ≤ d.w2 13108 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13108 ≤ 2 * (228 / 100 : ℝ) / 13108 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13108 ≤ 2 * (370 / 100 : ℝ) / 13108 := by
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
    (completeRAData (tableEnvelope C) 13108 165).locationBound 13108 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13108 165).energyBound 13108 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13108 165) (d.f1 13108 165) d.f2 ≤
      32 * (((4234360159 / 1000000000000000000) : ℝ) + (1412654123 / 1000000000000000000) + (42441493 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13108 165) (d.w1 13108 165)
      (d.w2 13108 165) ≤
      32 * (((1667283321 / 100000000000000000000) : ℝ) + (1186240207 / 100000000000000000000) + (43342169 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13108 165) (d.f1 13108 165) d.f2 ≤
      ((4234360159 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4234360159 / 1000000000000000000)) * ((1412654123 / 1000000000000000000)) * (126 / 100) +
      2 * (((1412654123 / 1000000000000000000)) ^ 2 + 2 * ((4234360159 / 1000000000000000000)) * ((42441493 / 125000000000000000))) +
      6 * ((1412654123 / 1000000000000000000)) * ((42441493 / 125000000000000000)) * (126 / 100) + 8 * ((42441493 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13108 165) (d.f1 13108 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13108 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13108 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13108 165) (d.f1 13108 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13108 165) (d.w1 13108 165) (d.w2 13108 165)
  have hwexpr0 : 0 ≤ d.w0 13108 165 + d.w1 13108 165 * √(π / 2) +
      2 * d.w2 13108 165 + energyR16 13108 *
      radiusPolynomialRoot16 (d.w0 13108 165) (d.w1 13108 165) (d.w2 13108 165) := by
    positivity
  constructor
  · change (13108 : ℝ) ^ 8 * (mA 13108 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13108 165) (d.f1 13108 165) d.f2 + locationR16 13108 *
        radiusPolynomialRoot16 (d.f0 13108 165) (d.f1 13108 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13108 : ℝ) ^ 8 * (mA 13108 : ℝ) ^ 8 *
        ((((4234360159 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4234360159 / 1000000000000000000)) * ((1412654123 / 1000000000000000000)) * (126 / 100) +
          2 * (((1412654123 / 1000000000000000000)) ^ 2 + 2 * ((4234360159 / 1000000000000000000)) * ((42441493 / 125000000000000000))) +
          6 * ((1412654123 / 1000000000000000000)) * ((42441493 / 125000000000000000)) * (126 / 100) + 8 * ((42441493 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13108) *
          (32 * (((4234360159 / 1000000000000000000) : ℝ) + (1412654123 / 1000000000000000000) + (42441493 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13108 : ℝ) ^ 16 *
      (d.w0 13108 165 + d.w1 13108 165 * √(π / 2) + 2 * d.w2 13108 165 +
        energyR16 13108 * radiusPolynomialRoot16 (d.w0 13108 165) (d.w1 13108 165)
          (d.w2 13108 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13108 : ℝ) ^ 16 *
        (((1667283321 / 100000000000000000000) : ℝ) + ((1186240207 / 100000000000000000000)) * (126 / 100) + 2 * ((43342169 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13108) *
          (32 * (((1667283321 / 100000000000000000000) : ℝ) + (1186240207 / 100000000000000000000) + (43342169 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13108

/-! A coarse bound on the actual paper statistics constant at dimension 13109. -/
namespace BstLean.Part266.Row13109
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13107 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13107 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13107 128 ≤ (13361 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13361 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13109) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13109 : ℕ))
    (by norm_num : (13109 : ℕ) ≤ 16384)
  have ht : paperTail256 13109 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13109 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13109 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13109 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13109 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13109 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13107 128 * √(2 / (13109 : ℝ)) *
      (√(13109 : ℝ) + paperT0 13109 + paperTail256 13109) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13109 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13109 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13109 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13107 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13107 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13109 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13109

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13109
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13109 (61 / 100) 165 (17 / (100 * 13109)) (26 / (10 * 13109)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13109 (61 / 100) 165 (17 / (100 * 13109)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (21665933 / 5000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (20659407 / 15625000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1982624273 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13109 / 13109 * (61 / 100)) ^ 4 * inverseRadius8 (13109 - 1) /
            envelopeGap 13109 (61 / 100) 165 (17 / (100 * 13109)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13109

namespace BstLean.Part266.Row13109
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13109 165 ≤ (21167757 / 5000000000000000)
  f1 : (tableEnvelope C).f1 13109 165 ≤ (88274027 / 62500000000000000)
  f2 : (tableEnvelope C).f2 ≤ (339467157 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13109 165 ≤ (1666901523 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13109 165 ≤ (592984311 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13109 165 ≤ (216661251 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (21665933 / 5000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (21665933 / 5000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (20659407 / 15625000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1982624273 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3601137 / 1000000000) : ℝ) ≤ √(17 / (100 * 13109) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13109) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (416326151 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3636209631 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13109) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13109) ≤ (107881117 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13109) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13109 * (165 : ℝ) ^ 2 + 26 / (10 * 13109) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13109) : ℝ)) (tA 13109 * 165 ^ 2 + 26 / (10 * 13109)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3601137 / 1000000000))) * ((21665933 / 5000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3601137 / 1000000000)) ^ 3) * ((20659407 / 15625000000000000000000))) + ((1982624273 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3601137 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13109) : ℝ)) d.D d.V d.P (√(tA 13109) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3601137 / 1000000000)) ^ 2 * (((416326151 / 200000000000000)) * ((3636209631 / 100000000000000000)))) + ((1982624273 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13109) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3601137 / 1000000000)) * ((21665933 / 5000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13109) : ℝ)) (tA 13109 * 165 ^ 2 + 26 / (10 * 13109)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((21665933 / 5000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3601137 / 1000000000)) ^ 2) * ((20659407 / 15625000000000000000000)) + ((1982624273 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13109) : ℝ)) (√(26 / (10 * 13109) : ℝ)) d.D d.V d.P (√(tA 13109) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3601137 / 1000000000)) * (((416326151 / 200000000000000)) * ((3636209631 / 100000000000000000))) + ((1982624273 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13109) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((21665933 / 5000000000000000000) : ℝ) + ((1982624273 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13109

namespace BstLean.Part266.Row13109
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13109 165 ∧
    0 ≤ (tableEnvelope C).f1 13109 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13109 165 ∧
    0 ≤ (tableEnvelope C).w1 13109 165 ∧ 0 ≤ (tableEnvelope C).w2 13109 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13109 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13109 165 ∧ 0 ≤ d.f1 13109 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13109 165 ∧ 0 ≤ d.w1 13109 165 ∧ 0 ≤ d.w2 13109 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13109 ≤ 2 * (228 / 100 : ℝ) / 13109 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13109 ≤ 2 * (370 / 100 : ℝ) / 13109 := by
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
    (completeRAData (tableEnvelope C) 13109 165).locationBound 13109 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13109 165).energyBound 13109 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13109 165) (d.f1 13109 165) d.f2 ≤
      32 * (((21167757 / 5000000000000000) : ℝ) + (88274027 / 62500000000000000) + (339467157 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13109 165) (d.w1 13109 165)
      (d.w2 13109 165) ≤
      32 * (((1666901523 / 100000000000000000000) : ℝ) + (592984311 / 50000000000000000000) + (216661251 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13109 165) (d.f1 13109 165) d.f2 ≤
      ((21167757 / 5000000000000000) : ℝ) ^ 2 + 2 * ((21167757 / 5000000000000000)) * ((88274027 / 62500000000000000)) * (126 / 100) +
      2 * (((88274027 / 62500000000000000)) ^ 2 + 2 * ((21167757 / 5000000000000000)) * ((339467157 / 1000000000000000000))) +
      6 * ((88274027 / 62500000000000000)) * ((339467157 / 1000000000000000000)) * (126 / 100) + 8 * ((339467157 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13109 165) (d.f1 13109 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13109 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13109 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13109 165) (d.f1 13109 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13109 165) (d.w1 13109 165) (d.w2 13109 165)
  have hwexpr0 : 0 ≤ d.w0 13109 165 + d.w1 13109 165 * √(π / 2) +
      2 * d.w2 13109 165 + energyR16 13109 *
      radiusPolynomialRoot16 (d.w0 13109 165) (d.w1 13109 165) (d.w2 13109 165) := by
    positivity
  constructor
  · change (13109 : ℝ) ^ 8 * (mA 13109 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13109 165) (d.f1 13109 165) d.f2 + locationR16 13109 *
        radiusPolynomialRoot16 (d.f0 13109 165) (d.f1 13109 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13109 : ℝ) ^ 8 * (mA 13109 : ℝ) ^ 8 *
        ((((21167757 / 5000000000000000) : ℝ) ^ 2 + 2 * ((21167757 / 5000000000000000)) * ((88274027 / 62500000000000000)) * (126 / 100) +
          2 * (((88274027 / 62500000000000000)) ^ 2 + 2 * ((21167757 / 5000000000000000)) * ((339467157 / 1000000000000000000))) +
          6 * ((88274027 / 62500000000000000)) * ((339467157 / 1000000000000000000)) * (126 / 100) + 8 * ((339467157 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13109) *
          (32 * (((21167757 / 5000000000000000) : ℝ) + (88274027 / 62500000000000000) + (339467157 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13109 : ℝ) ^ 16 *
      (d.w0 13109 165 + d.w1 13109 165 * √(π / 2) + 2 * d.w2 13109 165 +
        energyR16 13109 * radiusPolynomialRoot16 (d.w0 13109 165) (d.w1 13109 165)
          (d.w2 13109 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13109 : ℝ) ^ 16 *
        (((1666901523 / 100000000000000000000) : ℝ) + ((592984311 / 50000000000000000000)) * (126 / 100) + 2 * ((216661251 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13109) *
          (32 * (((1666901523 / 100000000000000000000) : ℝ) + (592984311 / 50000000000000000000) + (216661251 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13109

/-! A coarse bound on the actual paper statistics constant at dimension 13110. -/
namespace BstLean.Part266.Row13110
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13108 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13108 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13108 128 ≤ (13362 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13362 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13110) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13110 : ℕ))
    (by norm_num : (13110 : ℕ) ≤ 16384)
  have ht : paperTail256 13110 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13110 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13110 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13110 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13110 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13110 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13108 128 * √(2 / (13110 : ℝ)) *
      (√(13110 : ℝ) + paperT0 13110 + paperTail256 13110) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13110 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13110 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13110 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13108 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13108 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13110 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13110

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13110
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13110 (61 / 100) 165 (17 / (100 * 13110)) (26 / (10 * 13110)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13110 (61 / 100) 165 (17 / (100 * 13110)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (86643901 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1321798661 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (198140343 / 50000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13110 / 13110 * (61 / 100)) ^ 4 * inverseRadius8 (13110 - 1) /
            envelopeGap 13110 (61 / 100) 165 (17 / (100 * 13110)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13110

namespace BstLean.Part266.Row13110
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13110 165 ≤ (4232746303 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13110 165 ≤ (141211561 / 100000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (84850621 / 250000000000000000)
  w0 : (tableEnvelope C).w0 13110 165 ≤ (1666520539 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13110 165 ≤ (74106091 / 6250000000000000000)
  w2 : (tableEnvelope C).w2 13110 165 ≤ (27076459 / 6250000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (86643901 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (86643901 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1321798661 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (198140343 / 50000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3600999 / 1000000000) : ℝ) ≤ √(17 / (100 * 13110) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13110) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (83255703 / 40000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (908913727 / 25000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13110) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13110) ≤ (107872889 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13110) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13110 * (165 : ℝ) ^ 2 + 26 / (10 * 13110) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13110) : ℝ)) (tA 13110 * 165 ^ 2 + 26 / (10 * 13110)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3600999 / 1000000000))) * ((86643901 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3600999 / 1000000000)) ^ 3) * ((1321798661 / 1000000000000000000000000))) + ((198140343 / 50000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3600999 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13110) : ℝ)) d.D d.V d.P (√(tA 13110) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3600999 / 1000000000)) ^ 2 * (((83255703 / 40000000000000)) * ((908913727 / 25000000000000000)))) + ((198140343 / 50000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13110) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3600999 / 1000000000)) * ((86643901 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13110) : ℝ)) (tA 13110 * 165 ^ 2 + 26 / (10 * 13110)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((86643901 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3600999 / 1000000000)) ^ 2) * ((1321798661 / 1000000000000000000000000)) + ((198140343 / 50000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13110) : ℝ)) (√(26 / (10 * 13110) : ℝ)) d.D d.V d.P (√(tA 13110) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3600999 / 1000000000)) * (((83255703 / 40000000000000)) * ((908913727 / 25000000000000000))) + ((198140343 / 50000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13110) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((86643901 / 20000000000000000000) : ℝ) + ((198140343 / 50000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13110

namespace BstLean.Part266.Row13110
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13110 165 ∧
    0 ≤ (tableEnvelope C).f1 13110 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13110 165 ∧
    0 ≤ (tableEnvelope C).w1 13110 165 ∧ 0 ≤ (tableEnvelope C).w2 13110 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13110 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13110 165 ∧ 0 ≤ d.f1 13110 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13110 165 ∧ 0 ≤ d.w1 13110 165 ∧ 0 ≤ d.w2 13110 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13110 ≤ 2 * (228 / 100 : ℝ) / 13110 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13110 ≤ 2 * (370 / 100 : ℝ) / 13110 := by
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
    (completeRAData (tableEnvelope C) 13110 165).locationBound 13110 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13110 165).energyBound 13110 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13110 165) (d.f1 13110 165) d.f2 ≤
      32 * (((4232746303 / 1000000000000000000) : ℝ) + (141211561 / 100000000000000000) + (84850621 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13110 165) (d.w1 13110 165)
      (d.w2 13110 165) ≤
      32 * (((1666520539 / 100000000000000000000) : ℝ) + (74106091 / 6250000000000000000) + (27076459 / 6250000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13110 165) (d.f1 13110 165) d.f2 ≤
      ((4232746303 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4232746303 / 1000000000000000000)) * ((141211561 / 100000000000000000)) * (126 / 100) +
      2 * (((141211561 / 100000000000000000)) ^ 2 + 2 * ((4232746303 / 1000000000000000000)) * ((84850621 / 250000000000000000))) +
      6 * ((141211561 / 100000000000000000)) * ((84850621 / 250000000000000000)) * (126 / 100) + 8 * ((84850621 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13110 165) (d.f1 13110 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13110 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13110 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13110 165) (d.f1 13110 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13110 165) (d.w1 13110 165) (d.w2 13110 165)
  have hwexpr0 : 0 ≤ d.w0 13110 165 + d.w1 13110 165 * √(π / 2) +
      2 * d.w2 13110 165 + energyR16 13110 *
      radiusPolynomialRoot16 (d.w0 13110 165) (d.w1 13110 165) (d.w2 13110 165) := by
    positivity
  constructor
  · change (13110 : ℝ) ^ 8 * (mA 13110 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13110 165) (d.f1 13110 165) d.f2 + locationR16 13110 *
        radiusPolynomialRoot16 (d.f0 13110 165) (d.f1 13110 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13110 : ℝ) ^ 8 * (mA 13110 : ℝ) ^ 8 *
        ((((4232746303 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4232746303 / 1000000000000000000)) * ((141211561 / 100000000000000000)) * (126 / 100) +
          2 * (((141211561 / 100000000000000000)) ^ 2 + 2 * ((4232746303 / 1000000000000000000)) * ((84850621 / 250000000000000000))) +
          6 * ((141211561 / 100000000000000000)) * ((84850621 / 250000000000000000)) * (126 / 100) + 8 * ((84850621 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13110) *
          (32 * (((4232746303 / 1000000000000000000) : ℝ) + (141211561 / 100000000000000000) + (84850621 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13110 : ℝ) ^ 16 *
      (d.w0 13110 165 + d.w1 13110 165 * √(π / 2) + 2 * d.w2 13110 165 +
        energyR16 13110 * radiusPolynomialRoot16 (d.w0 13110 165) (d.w1 13110 165)
          (d.w2 13110 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13110 : ℝ) ^ 16 *
        (((1666520539 / 100000000000000000000) : ℝ) + ((74106091 / 6250000000000000000)) * (126 / 100) + 2 * ((27076459 / 6250000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13110) *
          (32 * (((1666520539 / 100000000000000000000) : ℝ) + (74106091 / 6250000000000000000) + (27076459 / 6250000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13110

/-! A coarse bound on the actual paper statistics constant at dimension 13111. -/
namespace BstLean.Part266.Row13111
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13109 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13109 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13109 128 ≤ (13363 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13363 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13111) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13111 : ℕ))
    (by norm_num : (13111 : ℕ) ≤ 16384)
  have ht : paperTail256 13111 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13111 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13111 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13111 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13111 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13111 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13109 128 * √(2 / (13111 : ℝ)) *
      (√(13111 : ℝ) + paperT0 13111 + paperTail256 13111) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13111 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13111 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13111 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13109 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13109 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13111 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13111

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13111
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13111 (61 / 100) 165 (17 / (100 * 13111)) (26 / (10 * 13111)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13111 (61 / 100) 165 (17 / (100 * 13111)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (21656019 / 5000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (330348857 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3960366867 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13111 / 13111 * (61 / 100)) ^ 4 * inverseRadius8 (13111 - 1) /
            envelopeGap 13111 (61 / 100) 165 (17 / (100 * 13111)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13111

namespace BstLean.Part266.Row13111
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13111 165 ≤ (4231938083 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13111 165 ≤ (1411846089 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (42417217 / 125000000000000000)
  w0 : (tableEnvelope C).w0 13111 165 ≤ (416534749 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 13111 165 ≤ (9261141 / 781250000000000000)
  w2 : (tableEnvelope C).w2 13111 165 ≤ (433124217 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (21656019 / 5000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (21656019 / 5000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (330348857 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3960366867 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1800431 / 500000000) : ℝ) ≤ √(17 / (100 * 13111) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13111) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (52028861 / 25000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36351003123 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13111) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13111) ≤ (107864661 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13111) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13111 * (165 : ℝ) ^ 2 + 26 / (10 * 13111) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13111) : ℝ)) (tA 13111 * 165 ^ 2 + 26 / (10 * 13111)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1800431 / 500000000))) * ((21656019 / 5000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1800431 / 500000000)) ^ 3) * ((330348857 / 250000000000000000000000))) + ((3960366867 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1800431 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13111) : ℝ)) d.D d.V d.P (√(tA 13111) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1800431 / 500000000)) ^ 2 * (((52028861 / 25000000000000)) * ((36351003123 / 1000000000000000000)))) + ((3960366867 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13111) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1800431 / 500000000)) * ((21656019 / 5000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13111) : ℝ)) (tA 13111 * 165 ^ 2 + 26 / (10 * 13111)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((21656019 / 5000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1800431 / 500000000)) ^ 2) * ((330348857 / 250000000000000000000000)) + ((3960366867 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13111) : ℝ)) (√(26 / (10 * 13111) : ℝ)) d.D d.V d.P (√(tA 13111) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1800431 / 500000000)) * (((52028861 / 25000000000000)) * ((36351003123 / 1000000000000000000))) + ((3960366867 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13111) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((21656019 / 5000000000000000000) : ℝ) + ((3960366867 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13111

namespace BstLean.Part266.Row13111
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13111 165 ∧
    0 ≤ (tableEnvelope C).f1 13111 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13111 165 ∧
    0 ≤ (tableEnvelope C).w1 13111 165 ∧ 0 ≤ (tableEnvelope C).w2 13111 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13111 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13111 165 ∧ 0 ≤ d.f1 13111 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13111 165 ∧ 0 ≤ d.w1 13111 165 ∧ 0 ≤ d.w2 13111 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13111 ≤ 2 * (228 / 100 : ℝ) / 13111 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13111 ≤ 2 * (370 / 100 : ℝ) / 13111 := by
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
    (completeRAData (tableEnvelope C) 13111 165).locationBound 13111 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13111 165).energyBound 13111 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13111 165) (d.f1 13111 165) d.f2 ≤
      32 * (((4231938083 / 1000000000000000000) : ℝ) + (1411846089 / 1000000000000000000) + (42417217 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13111 165) (d.w1 13111 165)
      (d.w2 13111 165) ≤
      32 * (((416534749 / 25000000000000000000) : ℝ) + (9261141 / 781250000000000000) + (433124217 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13111 165) (d.f1 13111 165) d.f2 ≤
      ((4231938083 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4231938083 / 1000000000000000000)) * ((1411846089 / 1000000000000000000)) * (126 / 100) +
      2 * (((1411846089 / 1000000000000000000)) ^ 2 + 2 * ((4231938083 / 1000000000000000000)) * ((42417217 / 125000000000000000))) +
      6 * ((1411846089 / 1000000000000000000)) * ((42417217 / 125000000000000000)) * (126 / 100) + 8 * ((42417217 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13111 165) (d.f1 13111 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13111 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13111 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13111 165) (d.f1 13111 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13111 165) (d.w1 13111 165) (d.w2 13111 165)
  have hwexpr0 : 0 ≤ d.w0 13111 165 + d.w1 13111 165 * √(π / 2) +
      2 * d.w2 13111 165 + energyR16 13111 *
      radiusPolynomialRoot16 (d.w0 13111 165) (d.w1 13111 165) (d.w2 13111 165) := by
    positivity
  constructor
  · change (13111 : ℝ) ^ 8 * (mA 13111 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13111 165) (d.f1 13111 165) d.f2 + locationR16 13111 *
        radiusPolynomialRoot16 (d.f0 13111 165) (d.f1 13111 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13111 : ℝ) ^ 8 * (mA 13111 : ℝ) ^ 8 *
        ((((4231938083 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4231938083 / 1000000000000000000)) * ((1411846089 / 1000000000000000000)) * (126 / 100) +
          2 * (((1411846089 / 1000000000000000000)) ^ 2 + 2 * ((4231938083 / 1000000000000000000)) * ((42417217 / 125000000000000000))) +
          6 * ((1411846089 / 1000000000000000000)) * ((42417217 / 125000000000000000)) * (126 / 100) + 8 * ((42417217 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13111) *
          (32 * (((4231938083 / 1000000000000000000) : ℝ) + (1411846089 / 1000000000000000000) + (42417217 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13111 : ℝ) ^ 16 *
      (d.w0 13111 165 + d.w1 13111 165 * √(π / 2) + 2 * d.w2 13111 165 +
        energyR16 13111 * radiusPolynomialRoot16 (d.w0 13111 165) (d.w1 13111 165)
          (d.w2 13111 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13111 : ℝ) ^ 16 *
        (((416534749 / 25000000000000000000) : ℝ) + ((9261141 / 781250000000000000)) * (126 / 100) + 2 * ((433124217 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13111) *
          (32 * (((416534749 / 25000000000000000000) : ℝ) + (9261141 / 781250000000000000) + (433124217 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13111

/-! A coarse bound on the actual paper statistics constant at dimension 13112. -/
namespace BstLean.Part266.Row13112
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13110 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13110 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13110 128 ≤ (13364 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13364 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13112) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13112 : ℕ))
    (by norm_num : (13112 : ℕ) ≤ 16384)
  have ht : paperTail256 13112 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13112 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13112 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13112 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13112 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13112 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13110 128 * √(2 / (13112 : ℝ)) *
      (√(13112 : ℝ) + paperT0 13112 + paperTail256 13112) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13112 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13112 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13112 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13110 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13110 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13112 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13112

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13112
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13112 (61 / 100) 165 (17 / (100 * 13112)) (26 / (10 * 13112)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13112 (61 / 100) 165 (17 / (100 * 13112)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (216510643 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (330248087 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (791585713 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13112 / 13112 * (61 / 100)) ^ 4 * inverseRadius8 (13112 - 1) /
            envelopeGap 13112 (61 / 100) 165 (17 / (100 * 13112)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13112

namespace BstLean.Part266.Row13112
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13112 165 ≤ (423113013 / 100000000000000000)
  f1 : (tableEnvelope C).f1 13112 165 ≤ (352894163 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (169636503 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13112 165 ≤ (1665757581 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13112 165 ≤ (1185154729 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13112 165 ≤ (2706407 / 625000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (216510643 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (216510643 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (330248087 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (791585713 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((144029 / 40000000) : ℝ) ≤ √(17 / (100 * 13112) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13112) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (16257159 / 7812500000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4543182303 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13112) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13112) ≤ (53928217 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13112) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13112 * (165 : ℝ) ^ 2 + 26 / (10 * 13112) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13112) : ℝ)) (tA 13112 * 165 ^ 2 + 26 / (10 * 13112)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((144029 / 40000000))) * ((216510643 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((144029 / 40000000)) ^ 3) * ((330248087 / 250000000000000000000000))) + ((791585713 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((144029 / 40000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13112) : ℝ)) d.D d.V d.P (√(tA 13112) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((144029 / 40000000)) ^ 2 * (((16257159 / 7812500000000)) * ((4543182303 / 125000000000000000)))) + ((791585713 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13112) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((144029 / 40000000)) * ((216510643 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13112) : ℝ)) (tA 13112 * 165 ^ 2 + 26 / (10 * 13112)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((216510643 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((144029 / 40000000)) ^ 2) * ((330248087 / 250000000000000000000000)) + ((791585713 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13112) : ℝ)) (√(26 / (10 * 13112) : ℝ)) d.D d.V d.P (√(tA 13112) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((144029 / 40000000)) * (((16257159 / 7812500000000)) * ((4543182303 / 125000000000000000))) + ((791585713 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13112) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((216510643 / 50000000000000000000) : ℝ) + ((791585713 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13112

namespace BstLean.Part266.Row13112
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13112 165 ∧
    0 ≤ (tableEnvelope C).f1 13112 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13112 165 ∧
    0 ≤ (tableEnvelope C).w1 13112 165 ∧ 0 ≤ (tableEnvelope C).w2 13112 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13112 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13112 165 ∧ 0 ≤ d.f1 13112 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13112 165 ∧ 0 ≤ d.w1 13112 165 ∧ 0 ≤ d.w2 13112 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13112 ≤ 2 * (228 / 100 : ℝ) / 13112 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13112 ≤ 2 * (370 / 100 : ℝ) / 13112 := by
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
    (completeRAData (tableEnvelope C) 13112 165).locationBound 13112 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13112 165).energyBound 13112 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13112 165) (d.f1 13112 165) d.f2 ≤
      32 * (((423113013 / 100000000000000000) : ℝ) + (352894163 / 250000000000000000) + (169636503 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13112 165) (d.w1 13112 165)
      (d.w2 13112 165) ≤
      32 * (((1665757581 / 100000000000000000000) : ℝ) + (1185154729 / 100000000000000000000) + (2706407 / 625000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13112 165) (d.f1 13112 165) d.f2 ≤
      ((423113013 / 100000000000000000) : ℝ) ^ 2 + 2 * ((423113013 / 100000000000000000)) * ((352894163 / 250000000000000000)) * (126 / 100) +
      2 * (((352894163 / 250000000000000000)) ^ 2 + 2 * ((423113013 / 100000000000000000)) * ((169636503 / 500000000000000000))) +
      6 * ((352894163 / 250000000000000000)) * ((169636503 / 500000000000000000)) * (126 / 100) + 8 * ((169636503 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13112 165) (d.f1 13112 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13112 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13112 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13112 165) (d.f1 13112 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13112 165) (d.w1 13112 165) (d.w2 13112 165)
  have hwexpr0 : 0 ≤ d.w0 13112 165 + d.w1 13112 165 * √(π / 2) +
      2 * d.w2 13112 165 + energyR16 13112 *
      radiusPolynomialRoot16 (d.w0 13112 165) (d.w1 13112 165) (d.w2 13112 165) := by
    positivity
  constructor
  · change (13112 : ℝ) ^ 8 * (mA 13112 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13112 165) (d.f1 13112 165) d.f2 + locationR16 13112 *
        radiusPolynomialRoot16 (d.f0 13112 165) (d.f1 13112 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13112 : ℝ) ^ 8 * (mA 13112 : ℝ) ^ 8 *
        ((((423113013 / 100000000000000000) : ℝ) ^ 2 + 2 * ((423113013 / 100000000000000000)) * ((352894163 / 250000000000000000)) * (126 / 100) +
          2 * (((352894163 / 250000000000000000)) ^ 2 + 2 * ((423113013 / 100000000000000000)) * ((169636503 / 500000000000000000))) +
          6 * ((352894163 / 250000000000000000)) * ((169636503 / 500000000000000000)) * (126 / 100) + 8 * ((169636503 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13112) *
          (32 * (((423113013 / 100000000000000000) : ℝ) + (352894163 / 250000000000000000) + (169636503 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13112 : ℝ) ^ 16 *
      (d.w0 13112 165 + d.w1 13112 165 * √(π / 2) + 2 * d.w2 13112 165 +
        energyR16 13112 * radiusPolynomialRoot16 (d.w0 13112 165) (d.w1 13112 165)
          (d.w2 13112 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13112 : ℝ) ^ 16 *
        (((1665757581 / 100000000000000000000) : ℝ) + ((1185154729 / 100000000000000000000)) * (126 / 100) + 2 * ((2706407 / 625000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13112) *
          (32 * (((1665757581 / 100000000000000000000) : ℝ) + (1185154729 / 100000000000000000000) + (2706407 / 625000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13112

/-! A coarse bound on the actual paper statistics constant at dimension 13113. -/
namespace BstLean.Part266.Row13113
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13111 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13111 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13111 128 ≤ (13365 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13365 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13113) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13113 : ℕ))
    (by norm_num : (13113 : ℕ) ≤ 16384)
  have ht : paperTail256 13113 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13113 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13113 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13113 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13113 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13113 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13111 128 * √(2 / (13113 : ℝ)) *
      (√(13113 : ℝ) + paperT0 13113 + paperTail256 13113) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13113 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13113 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13113 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13111 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13111 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13113 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13113

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13113
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13113 (61 / 100) 165 (17 / (100 * 13113)) (26 / (10 * 13113)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13113 (61 / 100) 165 (17 / (100 * 13113)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (216461111 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (660294711 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1977745977 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13113 / 13113 * (61 / 100)) ^ 4 * inverseRadius8 (13113 - 1) /
            envelopeGap 13113 (61 / 100) 165 (17 / (100 * 13113)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13113

namespace BstLean.Part266.Row13113
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13113 165 ≤ (2115161223 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13113 165 ≤ (1411307299 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (42401037 / 125000000000000000)
  w0 : (tableEnvelope C).w0 13113 165 ≤ (1665376293 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13113 165 ≤ (1184883497 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13113 165 ≤ (216463027 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (216461111 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (216461111 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (660294711 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1977745977 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((900147 / 250000000) : ℝ) ≤ √(17 / (100 * 13113) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13113) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (520169577 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18169957499 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13113) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13113) ≤ (107848209 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13113) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13113 * (165 : ℝ) ^ 2 + 26 / (10 * 13113) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13113) : ℝ)) (tA 13113 * 165 ^ 2 + 26 / (10 * 13113)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((900147 / 250000000))) * ((216461111 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((900147 / 250000000)) ^ 3) * ((660294711 / 500000000000000000000000))) + ((1977745977 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((900147 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13113) : ℝ)) d.D d.V d.P (√(tA 13113) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((900147 / 250000000)) ^ 2 * (((520169577 / 250000000000000)) * ((18169957499 / 500000000000000000)))) + ((1977745977 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13113) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((900147 / 250000000)) * ((216461111 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13113) : ℝ)) (tA 13113 * 165 ^ 2 + 26 / (10 * 13113)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((216461111 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((900147 / 250000000)) ^ 2) * ((660294711 / 500000000000000000000000)) + ((1977745977 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13113) : ℝ)) (√(26 / (10 * 13113) : ℝ)) d.D d.V d.P (√(tA 13113) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((900147 / 250000000)) * (((520169577 / 250000000000000)) * ((18169957499 / 500000000000000000))) + ((1977745977 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13113) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((216461111 / 50000000000000000000) : ℝ) + ((1977745977 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13113

namespace BstLean.Part266.Row13113
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13113 165 ∧
    0 ≤ (tableEnvelope C).f1 13113 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13113 165 ∧
    0 ≤ (tableEnvelope C).w1 13113 165 ∧ 0 ≤ (tableEnvelope C).w2 13113 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13113 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13113 165 ∧ 0 ≤ d.f1 13113 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13113 165 ∧ 0 ≤ d.w1 13113 165 ∧ 0 ≤ d.w2 13113 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13113 ≤ 2 * (228 / 100 : ℝ) / 13113 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13113 ≤ 2 * (370 / 100 : ℝ) / 13113 := by
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
    (completeRAData (tableEnvelope C) 13113 165).locationBound 13113 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13113 165).energyBound 13113 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13113 165) (d.f1 13113 165) d.f2 ≤
      32 * (((2115161223 / 500000000000000000) : ℝ) + (1411307299 / 1000000000000000000) + (42401037 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13113 165) (d.w1 13113 165)
      (d.w2 13113 165) ≤
      32 * (((1665376293 / 100000000000000000000) : ℝ) + (1184883497 / 100000000000000000000) + (216463027 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13113 165) (d.f1 13113 165) d.f2 ≤
      ((2115161223 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2115161223 / 500000000000000000)) * ((1411307299 / 1000000000000000000)) * (126 / 100) +
      2 * (((1411307299 / 1000000000000000000)) ^ 2 + 2 * ((2115161223 / 500000000000000000)) * ((42401037 / 125000000000000000))) +
      6 * ((1411307299 / 1000000000000000000)) * ((42401037 / 125000000000000000)) * (126 / 100) + 8 * ((42401037 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13113 165) (d.f1 13113 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13113 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13113 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13113 165) (d.f1 13113 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13113 165) (d.w1 13113 165) (d.w2 13113 165)
  have hwexpr0 : 0 ≤ d.w0 13113 165 + d.w1 13113 165 * √(π / 2) +
      2 * d.w2 13113 165 + energyR16 13113 *
      radiusPolynomialRoot16 (d.w0 13113 165) (d.w1 13113 165) (d.w2 13113 165) := by
    positivity
  constructor
  · change (13113 : ℝ) ^ 8 * (mA 13113 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13113 165) (d.f1 13113 165) d.f2 + locationR16 13113 *
        radiusPolynomialRoot16 (d.f0 13113 165) (d.f1 13113 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13113 : ℝ) ^ 8 * (mA 13113 : ℝ) ^ 8 *
        ((((2115161223 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2115161223 / 500000000000000000)) * ((1411307299 / 1000000000000000000)) * (126 / 100) +
          2 * (((1411307299 / 1000000000000000000)) ^ 2 + 2 * ((2115161223 / 500000000000000000)) * ((42401037 / 125000000000000000))) +
          6 * ((1411307299 / 1000000000000000000)) * ((42401037 / 125000000000000000)) * (126 / 100) + 8 * ((42401037 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13113) *
          (32 * (((2115161223 / 500000000000000000) : ℝ) + (1411307299 / 1000000000000000000) + (42401037 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13113 : ℝ) ^ 16 *
      (d.w0 13113 165 + d.w1 13113 165 * √(π / 2) + 2 * d.w2 13113 165 +
        energyR16 13113 * radiusPolynomialRoot16 (d.w0 13113 165) (d.w1 13113 165)
          (d.w2 13113 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13113 : ℝ) ^ 16 *
        (((1665376293 / 100000000000000000000) : ℝ) + ((1184883497 / 100000000000000000000)) * (126 / 100) + 2 * ((216463027 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13113) *
          (32 * (((1665376293 / 100000000000000000000) : ℝ) + (1184883497 / 100000000000000000000) + (216463027 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13113

/-! A coarse bound on the actual paper statistics constant at dimension 13114. -/
namespace BstLean.Part266.Row13114
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13112 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13112 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13112 128 ≤ (13366 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13366 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13114) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13114 : ℕ))
    (by norm_num : (13114 : ℕ) ≤ 16384)
  have ht : paperTail256 13114 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13114 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13114 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13114 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13114 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13114 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13112 128 * √(2 / (13114 : ℝ)) *
      (√(13114 : ℝ) + paperT0 13114 + paperTail256 13114) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13114 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13114 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13114 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13112 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13112 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13114 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13114

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13114
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13114 (61 / 100) 165 (17 / (100 * 13114)) (26 / (10 * 13114)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13114 (61 / 100) 165 (17 / (100 * 13114)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (432823187 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (26403733 / 20000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (494132129 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13114 / 13114 * (61 / 100)) ^ 4 * inverseRadius8 (13114 - 1) /
            envelopeGap 13114 (61 / 100) 165 (17 / (100 * 13114)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13114

namespace BstLean.Part266.Row13114
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13114 165 ≤ (4229518423 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13114 165 ≤ (1411038813 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (339143697 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13114 165 ≤ (208124477 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 13114 165 ≤ (29615317 / 2500000000000000000)
  w2 : (tableEnvelope C).w2 13114 165 ≤ (432827017 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (432823187 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (432823187 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (26403733 / 20000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (494132129 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((72009 / 20000000) : ℝ) ≤ √(17 / (100 * 13114) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13114) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2080440307 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7266874569 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13114) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13114) ≤ (21567997 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13114) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13114 * (165 : ℝ) ^ 2 + 26 / (10 * 13114) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13114) : ℝ)) (tA 13114 * 165 ^ 2 + 26 / (10 * 13114)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((72009 / 20000000))) * ((432823187 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((72009 / 20000000)) ^ 3) * ((26403733 / 20000000000000000000000))) + ((494132129 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((72009 / 20000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13114) : ℝ)) d.D d.V d.P (√(tA 13114) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((72009 / 20000000)) ^ 2 * (((2080440307 / 1000000000000000)) * ((7266874569 / 200000000000000000)))) + ((494132129 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13114) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((72009 / 20000000)) * ((432823187 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13114) : ℝ)) (tA 13114 * 165 ^ 2 + 26 / (10 * 13114)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((432823187 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((72009 / 20000000)) ^ 2) * ((26403733 / 20000000000000000000000)) + ((494132129 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13114) : ℝ)) (√(26 / (10 * 13114) : ℝ)) d.D d.V d.P (√(tA 13114) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((72009 / 20000000)) * (((2080440307 / 1000000000000000)) * ((7266874569 / 200000000000000000))) + ((494132129 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13114) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((432823187 / 100000000000000000000) : ℝ) + ((494132129 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13114

namespace BstLean.Part266.Row13114
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13114 165 ∧
    0 ≤ (tableEnvelope C).f1 13114 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13114 165 ∧
    0 ≤ (tableEnvelope C).w1 13114 165 ∧ 0 ≤ (tableEnvelope C).w2 13114 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13114 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13114 165 ∧ 0 ≤ d.f1 13114 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13114 165 ∧ 0 ≤ d.w1 13114 165 ∧ 0 ≤ d.w2 13114 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13114 ≤ 2 * (228 / 100 : ℝ) / 13114 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13114 ≤ 2 * (370 / 100 : ℝ) / 13114 := by
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
    (completeRAData (tableEnvelope C) 13114 165).locationBound 13114 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13114 165).energyBound 13114 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13114 165) (d.f1 13114 165) d.f2 ≤
      32 * (((4229518423 / 1000000000000000000) : ℝ) + (1411038813 / 1000000000000000000) + (339143697 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13114 165) (d.w1 13114 165)
      (d.w2 13114 165) ≤
      32 * (((208124477 / 12500000000000000000) : ℝ) + (29615317 / 2500000000000000000) + (432827017 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13114 165) (d.f1 13114 165) d.f2 ≤
      ((4229518423 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4229518423 / 1000000000000000000)) * ((1411038813 / 1000000000000000000)) * (126 / 100) +
      2 * (((1411038813 / 1000000000000000000)) ^ 2 + 2 * ((4229518423 / 1000000000000000000)) * ((339143697 / 1000000000000000000))) +
      6 * ((1411038813 / 1000000000000000000)) * ((339143697 / 1000000000000000000)) * (126 / 100) + 8 * ((339143697 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13114 165) (d.f1 13114 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13114 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13114 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13114 165) (d.f1 13114 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13114 165) (d.w1 13114 165) (d.w2 13114 165)
  have hwexpr0 : 0 ≤ d.w0 13114 165 + d.w1 13114 165 * √(π / 2) +
      2 * d.w2 13114 165 + energyR16 13114 *
      radiusPolynomialRoot16 (d.w0 13114 165) (d.w1 13114 165) (d.w2 13114 165) := by
    positivity
  constructor
  · change (13114 : ℝ) ^ 8 * (mA 13114 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13114 165) (d.f1 13114 165) d.f2 + locationR16 13114 *
        radiusPolynomialRoot16 (d.f0 13114 165) (d.f1 13114 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13114 : ℝ) ^ 8 * (mA 13114 : ℝ) ^ 8 *
        ((((4229518423 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4229518423 / 1000000000000000000)) * ((1411038813 / 1000000000000000000)) * (126 / 100) +
          2 * (((1411038813 / 1000000000000000000)) ^ 2 + 2 * ((4229518423 / 1000000000000000000)) * ((339143697 / 1000000000000000000))) +
          6 * ((1411038813 / 1000000000000000000)) * ((339143697 / 1000000000000000000)) * (126 / 100) + 8 * ((339143697 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13114) *
          (32 * (((4229518423 / 1000000000000000000) : ℝ) + (1411038813 / 1000000000000000000) + (339143697 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13114 : ℝ) ^ 16 *
      (d.w0 13114 165 + d.w1 13114 165 * √(π / 2) + 2 * d.w2 13114 165 +
        energyR16 13114 * radiusPolynomialRoot16 (d.w0 13114 165) (d.w1 13114 165)
          (d.w2 13114 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13114 : ℝ) ^ 16 *
        (((208124477 / 12500000000000000000) : ℝ) + ((29615317 / 2500000000000000000)) * (126 / 100) + 2 * ((432827017 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13114) *
          (32 * (((208124477 / 12500000000000000000) : ℝ) + (29615317 / 2500000000000000000) + (432827017 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13114

/-! A coarse bound on the actual paper statistics constant at dimension 13115. -/
namespace BstLean.Part266.Row13115
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13113 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13113 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13113 128 ≤ (13367 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13367 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13115) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13115 : ℕ))
    (by norm_num : (13115 : ℕ) ≤ 16384)
  have ht : paperTail256 13115 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13115 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13115 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13115 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13115 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13115 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13113 128 * √(2 / (13115 : ℝ)) *
      (√(13115 : ℝ) + paperT0 13115 + paperTail256 13115) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13115 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13115 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13115 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13113 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13113 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13115 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13115

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13115
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13115 (61 / 100) 165 (17 / (100 * 13115)) (26 / (10 * 13115)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13115 (61 / 100) 165 (17 / (100 * 13115)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (432724183 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1319784031 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1975311899 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13115 / 13115 * (61 / 100)) ^ 4 * inverseRadius8 (13115 - 1) /
            envelopeGap 13115 (61 / 100) 165 (17 / (100 * 13115)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13115

namespace BstLean.Part266.Row13115
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13115 165 ≤ (1057177819 / 250000000000000000)
  f1 : (tableEnvelope C).f1 13115 165 ≤ (352692407 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (339079023 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13115 165 ≤ (832307391 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13115 165 ≤ (148042703 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 13115 165 ≤ (43272801 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (432724183 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (432724183 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1319784031 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1975311899 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3600313 / 1000000000) : ℝ) ≤ √(17 / (100 * 13115) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13115) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1040101177 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36328831953 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13115) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13115) ≤ (107831763 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13115) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13115 * (165 : ℝ) ^ 2 + 26 / (10 * 13115) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13115) : ℝ)) (tA 13115 * 165 ^ 2 + 26 / (10 * 13115)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3600313 / 1000000000))) * ((432724183 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3600313 / 1000000000)) ^ 3) * ((1319784031 / 1000000000000000000000000))) + ((1975311899 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3600313 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13115) : ℝ)) d.D d.V d.P (√(tA 13115) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3600313 / 1000000000)) ^ 2 * (((1040101177 / 500000000000000)) * ((36328831953 / 1000000000000000000)))) + ((1975311899 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13115) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3600313 / 1000000000)) * ((432724183 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13115) : ℝ)) (tA 13115 * 165 ^ 2 + 26 / (10 * 13115)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((432724183 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3600313 / 1000000000)) ^ 2) * ((1319784031 / 1000000000000000000000000)) + ((1975311899 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13115) : ℝ)) (√(26 / (10 * 13115) : ℝ)) d.D d.V d.P (√(tA 13115) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3600313 / 1000000000)) * (((1040101177 / 500000000000000)) * ((36328831953 / 1000000000000000000))) + ((1975311899 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13115) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((432724183 / 100000000000000000000) : ℝ) + ((1975311899 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13115

namespace BstLean.Part266.Row13115
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13115 165 ∧
    0 ≤ (tableEnvelope C).f1 13115 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13115 165 ∧
    0 ≤ (tableEnvelope C).w1 13115 165 ∧ 0 ≤ (tableEnvelope C).w2 13115 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13115 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13115 165 ∧ 0 ≤ d.f1 13115 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13115 165 ∧ 0 ≤ d.w1 13115 165 ∧ 0 ≤ d.w2 13115 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13115 ≤ 2 * (228 / 100 : ℝ) / 13115 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13115 ≤ 2 * (370 / 100 : ℝ) / 13115 := by
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
    (completeRAData (tableEnvelope C) 13115 165).locationBound 13115 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13115 165).energyBound 13115 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13115 165) (d.f1 13115 165) d.f2 ≤
      32 * (((1057177819 / 250000000000000000) : ℝ) + (352692407 / 250000000000000000) + (339079023 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13115 165) (d.w1 13115 165)
      (d.w2 13115 165) ≤
      32 * (((832307391 / 50000000000000000000) : ℝ) + (148042703 / 12500000000000000000) + (43272801 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13115 165) (d.f1 13115 165) d.f2 ≤
      ((1057177819 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1057177819 / 250000000000000000)) * ((352692407 / 250000000000000000)) * (126 / 100) +
      2 * (((352692407 / 250000000000000000)) ^ 2 + 2 * ((1057177819 / 250000000000000000)) * ((339079023 / 1000000000000000000))) +
      6 * ((352692407 / 250000000000000000)) * ((339079023 / 1000000000000000000)) * (126 / 100) + 8 * ((339079023 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13115 165) (d.f1 13115 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13115 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13115 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13115 165) (d.f1 13115 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13115 165) (d.w1 13115 165) (d.w2 13115 165)
  have hwexpr0 : 0 ≤ d.w0 13115 165 + d.w1 13115 165 * √(π / 2) +
      2 * d.w2 13115 165 + energyR16 13115 *
      radiusPolynomialRoot16 (d.w0 13115 165) (d.w1 13115 165) (d.w2 13115 165) := by
    positivity
  constructor
  · change (13115 : ℝ) ^ 8 * (mA 13115 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13115 165) (d.f1 13115 165) d.f2 + locationR16 13115 *
        radiusPolynomialRoot16 (d.f0 13115 165) (d.f1 13115 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13115 : ℝ) ^ 8 * (mA 13115 : ℝ) ^ 8 *
        ((((1057177819 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1057177819 / 250000000000000000)) * ((352692407 / 250000000000000000)) * (126 / 100) +
          2 * (((352692407 / 250000000000000000)) ^ 2 + 2 * ((1057177819 / 250000000000000000)) * ((339079023 / 1000000000000000000))) +
          6 * ((352692407 / 250000000000000000)) * ((339079023 / 1000000000000000000)) * (126 / 100) + 8 * ((339079023 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13115) *
          (32 * (((1057177819 / 250000000000000000) : ℝ) + (352692407 / 250000000000000000) + (339079023 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13115 : ℝ) ^ 16 *
      (d.w0 13115 165 + d.w1 13115 165 * √(π / 2) + 2 * d.w2 13115 165 +
        energyR16 13115 * radiusPolynomialRoot16 (d.w0 13115 165) (d.w1 13115 165)
          (d.w2 13115 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13115 : ℝ) ^ 16 *
        (((832307391 / 50000000000000000000) : ℝ) + ((148042703 / 12500000000000000000)) * (126 / 100) + 2 * ((43272801 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13115) *
          (32 * (((832307391 / 50000000000000000000) : ℝ) + (148042703 / 12500000000000000000) + (43272801 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13115

/-! A coarse bound on the actual paper statistics constant at dimension 13116. -/
namespace BstLean.Part266.Row13116
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13114 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13114 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13114 128 ≤ (13368 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13368 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13116) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13116 : ℕ))
    (by norm_num : (13116 : ℕ) ≤ 16384)
  have ht : paperTail256 13116 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13116 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13116 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13116 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13116 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13116 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13114 128 * √(2 / (13116 : ℝ)) *
      (√(13116 : ℝ) + paperT0 13116 + paperTail256 13116) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13116 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13116 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13116 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13114 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13114 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13116 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13116

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13116
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13116 (61 / 100) 165 (17 / (100 * 13116)) (26 / (10 * 13116)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13116 (61 / 100) 165 (17 / (100 * 13116)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (43262521 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (659690783 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3948192251 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13116 / 13116 * (61 / 100)) ^ 4 * inverseRadius8 (13116 - 1) /
            envelopeGap 13116 (61 / 100) 165 (17 / (100 * 13116)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13116

namespace BstLean.Part266.Row13116
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13116 165 ≤ (10569761 / 2500000000000000)
  f1 : (tableEnvelope C).f1 13116 165 ≤ (88156283 / 62500000000000000)
  f2 : (tableEnvelope C).f2 ≤ (339014369 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13116 165 ≤ (13313871 / 800000000000000000)
  w1 : (tableEnvelope C).w1 13116 165 ≤ (1156319 / 97656250000000000)
  w2 : (tableEnvelope C).w2 13116 165 ≤ (86525807 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (43262521 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (43262521 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (659690783 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3948192251 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((225011 / 62500000) : ℝ) ≤ √(17 / (100 * 13116) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13116) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2079964447 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7264658467 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13116) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13116) ≤ (107823541 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13116) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13116 * (165 : ℝ) ^ 2 + 26 / (10 * 13116) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13116) : ℝ)) (tA 13116 * 165 ^ 2 + 26 / (10 * 13116)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((225011 / 62500000))) * ((43262521 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((225011 / 62500000)) ^ 3) * ((659690783 / 500000000000000000000000))) + ((3948192251 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((225011 / 62500000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13116) : ℝ)) d.D d.V d.P (√(tA 13116) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((225011 / 62500000)) ^ 2 * (((2079964447 / 1000000000000000)) * ((7264658467 / 200000000000000000)))) + ((3948192251 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13116) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((225011 / 62500000)) * ((43262521 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13116) : ℝ)) (tA 13116 * 165 ^ 2 + 26 / (10 * 13116)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((43262521 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((225011 / 62500000)) ^ 2) * ((659690783 / 500000000000000000000000)) + ((3948192251 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13116) : ℝ)) (√(26 / (10 * 13116) : ℝ)) d.D d.V d.P (√(tA 13116) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((225011 / 62500000)) * (((2079964447 / 1000000000000000)) * ((7264658467 / 200000000000000000))) + ((3948192251 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13116) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((43262521 / 10000000000000000000) : ℝ) + ((3948192251 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13116

namespace BstLean.Part266.Row13116
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13116 165 ∧
    0 ≤ (tableEnvelope C).f1 13116 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13116 165 ∧
    0 ≤ (tableEnvelope C).w1 13116 165 ∧ 0 ≤ (tableEnvelope C).w2 13116 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13116 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13116 165 ∧ 0 ≤ d.f1 13116 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13116 165 ∧ 0 ≤ d.w1 13116 165 ∧ 0 ≤ d.w2 13116 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13116 ≤ 2 * (228 / 100 : ℝ) / 13116 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13116 ≤ 2 * (370 / 100 : ℝ) / 13116 := by
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
    (completeRAData (tableEnvelope C) 13116 165).locationBound 13116 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13116 165).energyBound 13116 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13116 165) (d.f1 13116 165) d.f2 ≤
      32 * (((10569761 / 2500000000000000) : ℝ) + (88156283 / 62500000000000000) + (339014369 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13116 165) (d.w1 13116 165)
      (d.w2 13116 165) ≤
      32 * (((13313871 / 800000000000000000) : ℝ) + (1156319 / 97656250000000000) + (86525807 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13116 165) (d.f1 13116 165) d.f2 ≤
      ((10569761 / 2500000000000000) : ℝ) ^ 2 + 2 * ((10569761 / 2500000000000000)) * ((88156283 / 62500000000000000)) * (126 / 100) +
      2 * (((88156283 / 62500000000000000)) ^ 2 + 2 * ((10569761 / 2500000000000000)) * ((339014369 / 1000000000000000000))) +
      6 * ((88156283 / 62500000000000000)) * ((339014369 / 1000000000000000000)) * (126 / 100) + 8 * ((339014369 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13116 165) (d.f1 13116 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13116 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13116 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13116 165) (d.f1 13116 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13116 165) (d.w1 13116 165) (d.w2 13116 165)
  have hwexpr0 : 0 ≤ d.w0 13116 165 + d.w1 13116 165 * √(π / 2) +
      2 * d.w2 13116 165 + energyR16 13116 *
      radiusPolynomialRoot16 (d.w0 13116 165) (d.w1 13116 165) (d.w2 13116 165) := by
    positivity
  constructor
  · change (13116 : ℝ) ^ 8 * (mA 13116 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13116 165) (d.f1 13116 165) d.f2 + locationR16 13116 *
        radiusPolynomialRoot16 (d.f0 13116 165) (d.f1 13116 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13116 : ℝ) ^ 8 * (mA 13116 : ℝ) ^ 8 *
        ((((10569761 / 2500000000000000) : ℝ) ^ 2 + 2 * ((10569761 / 2500000000000000)) * ((88156283 / 62500000000000000)) * (126 / 100) +
          2 * (((88156283 / 62500000000000000)) ^ 2 + 2 * ((10569761 / 2500000000000000)) * ((339014369 / 1000000000000000000))) +
          6 * ((88156283 / 62500000000000000)) * ((339014369 / 1000000000000000000)) * (126 / 100) + 8 * ((339014369 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13116) *
          (32 * (((10569761 / 2500000000000000) : ℝ) + (88156283 / 62500000000000000) + (339014369 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13116 : ℝ) ^ 16 *
      (d.w0 13116 165 + d.w1 13116 165 * √(π / 2) + 2 * d.w2 13116 165 +
        energyR16 13116 * radiusPolynomialRoot16 (d.w0 13116 165) (d.w1 13116 165)
          (d.w2 13116 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13116 : ℝ) ^ 16 *
        (((13313871 / 800000000000000000) : ℝ) + ((1156319 / 97656250000000000)) * (126 / 100) + 2 * ((86525807 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13116) *
          (32 * (((13313871 / 800000000000000000) : ℝ) + (1156319 / 97656250000000000) + (86525807 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13116

/-! A coarse bound on the actual paper statistics constant at dimension 13117. -/
namespace BstLean.Part266.Row13117
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13115 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13115 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13115 128 ≤ (13369 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13369 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13117) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13117 : ℕ))
    (by norm_num : (13117 : ℕ) ≤ 16384)
  have ht : paperTail256 13117 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13117 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13117 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13117 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13117 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13117 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13115 128 * √(2 / (13117 : ℝ)) *
      (√(13117 : ℝ) + paperT0 13117 + paperTail256 13117) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13117 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13117 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13117 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13115 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13115 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13117 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13117

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13117
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13117 (61 / 100) 165 (17 / (100 * 13117)) (26 / (10 * 13117)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13117 (61 / 100) 165 (17 / (100 * 13117)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (216263133 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (659489627 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (986440597 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13117 / 13117 * (61 / 100)) ^ 4 * inverseRadius8 (13117 - 1) /
            envelopeGap 13117 (61 / 100) 165 (17 / (100 * 13117)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13117

namespace BstLean.Part266.Row13117
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13117 165 ≤ (211355059 / 50000000000000000)
  f1 : (tableEnvelope C).f1 13117 165 ≤ (705116147 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (338949827 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13117 165 ≤ (1663853779 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13117 165 ≤ (147975013 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 13117 165 ≤ (432530089 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (216263133 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (216263133 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (659489627 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (986440597 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1800019 / 500000000) : ℝ) ≤ √(17 / (100 * 13117) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13117) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2079726583 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18158876989 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13117) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13117) ≤ (107815321 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13117) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13117 * (165 : ℝ) ^ 2 + 26 / (10 * 13117) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13117) : ℝ)) (tA 13117 * 165 ^ 2 + 26 / (10 * 13117)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1800019 / 500000000))) * ((216263133 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1800019 / 500000000)) ^ 3) * ((659489627 / 500000000000000000000000))) + ((986440597 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1800019 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13117) : ℝ)) d.D d.V d.P (√(tA 13117) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1800019 / 500000000)) ^ 2 * (((2079726583 / 1000000000000000)) * ((18158876989 / 500000000000000000)))) + ((986440597 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13117) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1800019 / 500000000)) * ((216263133 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13117) : ℝ)) (tA 13117 * 165 ^ 2 + 26 / (10 * 13117)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((216263133 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1800019 / 500000000)) ^ 2) * ((659489627 / 500000000000000000000000)) + ((986440597 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13117) : ℝ)) (√(26 / (10 * 13117) : ℝ)) d.D d.V d.P (√(tA 13117) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1800019 / 500000000)) * (((2079726583 / 1000000000000000)) * ((18158876989 / 500000000000000000))) + ((986440597 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13117) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((216263133 / 50000000000000000000) : ℝ) + ((986440597 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13117

namespace BstLean.Part266.Row13117
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13117 165 ∧
    0 ≤ (tableEnvelope C).f1 13117 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13117 165 ∧
    0 ≤ (tableEnvelope C).w1 13117 165 ∧ 0 ≤ (tableEnvelope C).w2 13117 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13117 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13117 165 ∧ 0 ≤ d.f1 13117 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13117 165 ∧ 0 ≤ d.w1 13117 165 ∧ 0 ≤ d.w2 13117 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13117 ≤ 2 * (228 / 100 : ℝ) / 13117 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13117 ≤ 2 * (370 / 100 : ℝ) / 13117 := by
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
    (completeRAData (tableEnvelope C) 13117 165).locationBound 13117 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13117 165).energyBound 13117 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13117 165) (d.f1 13117 165) d.f2 ≤
      32 * (((211355059 / 50000000000000000) : ℝ) + (705116147 / 500000000000000000) + (338949827 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13117 165) (d.w1 13117 165)
      (d.w2 13117 165) ≤
      32 * (((1663853779 / 100000000000000000000) : ℝ) + (147975013 / 12500000000000000000) + (432530089 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13117 165) (d.f1 13117 165) d.f2 ≤
      ((211355059 / 50000000000000000) : ℝ) ^ 2 + 2 * ((211355059 / 50000000000000000)) * ((705116147 / 500000000000000000)) * (126 / 100) +
      2 * (((705116147 / 500000000000000000)) ^ 2 + 2 * ((211355059 / 50000000000000000)) * ((338949827 / 1000000000000000000))) +
      6 * ((705116147 / 500000000000000000)) * ((338949827 / 1000000000000000000)) * (126 / 100) + 8 * ((338949827 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13117 165) (d.f1 13117 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13117 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13117 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13117 165) (d.f1 13117 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13117 165) (d.w1 13117 165) (d.w2 13117 165)
  have hwexpr0 : 0 ≤ d.w0 13117 165 + d.w1 13117 165 * √(π / 2) +
      2 * d.w2 13117 165 + energyR16 13117 *
      radiusPolynomialRoot16 (d.w0 13117 165) (d.w1 13117 165) (d.w2 13117 165) := by
    positivity
  constructor
  · change (13117 : ℝ) ^ 8 * (mA 13117 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13117 165) (d.f1 13117 165) d.f2 + locationR16 13117 *
        radiusPolynomialRoot16 (d.f0 13117 165) (d.f1 13117 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13117 : ℝ) ^ 8 * (mA 13117 : ℝ) ^ 8 *
        ((((211355059 / 50000000000000000) : ℝ) ^ 2 + 2 * ((211355059 / 50000000000000000)) * ((705116147 / 500000000000000000)) * (126 / 100) +
          2 * (((705116147 / 500000000000000000)) ^ 2 + 2 * ((211355059 / 50000000000000000)) * ((338949827 / 1000000000000000000))) +
          6 * ((705116147 / 500000000000000000)) * ((338949827 / 1000000000000000000)) * (126 / 100) + 8 * ((338949827 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13117) *
          (32 * (((211355059 / 50000000000000000) : ℝ) + (705116147 / 500000000000000000) + (338949827 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13117 : ℝ) ^ 16 *
      (d.w0 13117 165 + d.w1 13117 165 * √(π / 2) + 2 * d.w2 13117 165 +
        energyR16 13117 * radiusPolynomialRoot16 (d.w0 13117 165) (d.w1 13117 165)
          (d.w2 13117 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13117 : ℝ) ^ 16 *
        (((1663853779 / 100000000000000000000) : ℝ) + ((147975013 / 12500000000000000000)) * (126 / 100) + 2 * ((432530089 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13117) *
          (32 * (((1663853779 / 100000000000000000000) : ℝ) + (147975013 / 12500000000000000000) + (432530089 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13117

/-! A coarse bound on the actual paper statistics constant at dimension 13118. -/
namespace BstLean.Part266.Row13118
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13116 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13116 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13116 128 ≤ (13370 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13370 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13118) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13118 : ℕ))
    (by norm_num : (13118 : ℕ) ≤ 16384)
  have ht : paperTail256 13118 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13118 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13118 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13118 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13118 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13118 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13116 128 * √(2 / (13118 : ℝ)) *
      (√(13118 : ℝ) + paperT0 13118 + paperTail256 13118) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13118 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13118 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13118 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13116 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13116 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13118 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13118

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13118
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13118 (61 / 100) 165 (17 / (100 * 13118)) (26 / (10 * 13118)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13118 (61 / 100) 165 (17 / (100 * 13118)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (432427353 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (164822137 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (394333421 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13118 / 13118 * (61 / 100)) ^ 4 * inverseRadius8 (13118 - 1) /
            envelopeGap 13118 (61 / 100) 165 (17 / (100 * 13118)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13118

namespace BstLean.Part266.Row13118
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13118 165 ≤ (4226294841 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13118 165 ≤ (1409963363 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (33888521 / 100000000000000000)
  w0 : (tableEnvelope C).w0 13118 165 ≤ (831736563 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13118 165 ≤ (36985291 / 3125000000000000000)
  w2 : (tableEnvelope C).w2 13118 165 ≤ (432431173 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (432427353 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (432427353 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (164822137 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (394333421 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3599901 / 1000000000) : ℝ) ≤ √(17 / (100 * 13118) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13118) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2079488767 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18156108449 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13118) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13118) ≤ (53903551 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13118) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13118 * (165 : ℝ) ^ 2 + 26 / (10 * 13118) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13118) : ℝ)) (tA 13118 * 165 ^ 2 + 26 / (10 * 13118)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3599901 / 1000000000))) * ((432427353 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3599901 / 1000000000)) ^ 3) * ((164822137 / 125000000000000000000000))) + ((394333421 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3599901 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13118) : ℝ)) d.D d.V d.P (√(tA 13118) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3599901 / 1000000000)) ^ 2 * (((2079488767 / 1000000000000000)) * ((18156108449 / 500000000000000000)))) + ((394333421 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13118) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3599901 / 1000000000)) * ((432427353 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13118) : ℝ)) (tA 13118 * 165 ^ 2 + 26 / (10 * 13118)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((432427353 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3599901 / 1000000000)) ^ 2) * ((164822137 / 125000000000000000000000)) + ((394333421 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13118) : ℝ)) (√(26 / (10 * 13118) : ℝ)) d.D d.V d.P (√(tA 13118) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3599901 / 1000000000)) * (((2079488767 / 1000000000000000)) * ((18156108449 / 500000000000000000))) + ((394333421 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13118) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((432427353 / 100000000000000000000) : ℝ) + ((394333421 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13118

namespace BstLean.Part266.Row13118
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13118 165 ∧
    0 ≤ (tableEnvelope C).f1 13118 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13118 165 ∧
    0 ≤ (tableEnvelope C).w1 13118 165 ∧ 0 ≤ (tableEnvelope C).w2 13118 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13118 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13118 165 ∧ 0 ≤ d.f1 13118 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13118 165 ∧ 0 ≤ d.w1 13118 165 ∧ 0 ≤ d.w2 13118 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13118 ≤ 2 * (228 / 100 : ℝ) / 13118 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13118 ≤ 2 * (370 / 100 : ℝ) / 13118 := by
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
    (completeRAData (tableEnvelope C) 13118 165).locationBound 13118 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13118 165).energyBound 13118 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13118 165) (d.f1 13118 165) d.f2 ≤
      32 * (((4226294841 / 1000000000000000000) : ℝ) + (1409963363 / 1000000000000000000) + (33888521 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13118 165) (d.w1 13118 165)
      (d.w2 13118 165) ≤
      32 * (((831736563 / 50000000000000000000) : ℝ) + (36985291 / 3125000000000000000) + (432431173 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13118 165) (d.f1 13118 165) d.f2 ≤
      ((4226294841 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4226294841 / 1000000000000000000)) * ((1409963363 / 1000000000000000000)) * (126 / 100) +
      2 * (((1409963363 / 1000000000000000000)) ^ 2 + 2 * ((4226294841 / 1000000000000000000)) * ((33888521 / 100000000000000000))) +
      6 * ((1409963363 / 1000000000000000000)) * ((33888521 / 100000000000000000)) * (126 / 100) + 8 * ((33888521 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13118 165) (d.f1 13118 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13118 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13118 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13118 165) (d.f1 13118 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13118 165) (d.w1 13118 165) (d.w2 13118 165)
  have hwexpr0 : 0 ≤ d.w0 13118 165 + d.w1 13118 165 * √(π / 2) +
      2 * d.w2 13118 165 + energyR16 13118 *
      radiusPolynomialRoot16 (d.w0 13118 165) (d.w1 13118 165) (d.w2 13118 165) := by
    positivity
  constructor
  · change (13118 : ℝ) ^ 8 * (mA 13118 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13118 165) (d.f1 13118 165) d.f2 + locationR16 13118 *
        radiusPolynomialRoot16 (d.f0 13118 165) (d.f1 13118 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13118 : ℝ) ^ 8 * (mA 13118 : ℝ) ^ 8 *
        ((((4226294841 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4226294841 / 1000000000000000000)) * ((1409963363 / 1000000000000000000)) * (126 / 100) +
          2 * (((1409963363 / 1000000000000000000)) ^ 2 + 2 * ((4226294841 / 1000000000000000000)) * ((33888521 / 100000000000000000))) +
          6 * ((1409963363 / 1000000000000000000)) * ((33888521 / 100000000000000000)) * (126 / 100) + 8 * ((33888521 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13118) *
          (32 * (((4226294841 / 1000000000000000000) : ℝ) + (1409963363 / 1000000000000000000) + (33888521 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13118 : ℝ) ^ 16 *
      (d.w0 13118 165 + d.w1 13118 165 * √(π / 2) + 2 * d.w2 13118 165 +
        energyR16 13118 * radiusPolynomialRoot16 (d.w0 13118 165) (d.w1 13118 165)
          (d.w2 13118 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13118 : ℝ) ^ 16 *
        (((831736563 / 50000000000000000000) : ℝ) + ((36985291 / 3125000000000000000)) * (126 / 100) + 2 * ((432431173 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13118) *
          (32 * (((831736563 / 50000000000000000000) : ℝ) + (36985291 / 3125000000000000000) + (432431173 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13118

/-! A coarse bound on the actual paper statistics constant at dimension 13119. -/
namespace BstLean.Part266.Row13119
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13117 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13117 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13117 128 ≤ (13371 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13371 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13119) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13119 : ℕ))
    (by norm_num : (13119 : ℕ) ≤ 16384)
  have ht : paperTail256 13119 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13119 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13119 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13119 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13119 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13119 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13117 128 * √(2 / (13119 : ℝ)) *
      (√(13119 : ℝ) + paperT0 13119 + paperTail256 13119) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13119 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13119 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13119 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13117 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13117 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13119 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13119

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13119
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13119 (61 / 100) 165 (17 / (100 * 13119)) (26 / (10 * 13119)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13119 (61 / 100) 165 (17 / (100 * 13119)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (43232847 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1318175091 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1970453857 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13119 / 13119 * (61 / 100)) ^ 4 * inverseRadius8 (13119 - 1) /
            envelopeGap 13119 (61 / 100) 165 (17 / (100 * 13119)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13119

namespace BstLean.Part266.Row13119
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13119 165 ≤ (4225488769 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13119 165 ≤ (281938903 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (84705153 / 250000000000000000)
  w0 : (tableEnvelope C).w0 13119 165 ≤ (1663092599 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13119 165 ≤ (1183258607 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13119 165 ≤ (844399 / 195312500000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (43232847 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (43232847 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1318175091 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1970453857 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((899941 / 250000000) : ℝ) ≤ √(17 / (100 * 13119) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13119) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (415850199 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (907667027 / 25000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13119) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13119) ≤ (21559777 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13119) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13119 * (165 : ℝ) ^ 2 + 26 / (10 * 13119) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13119) : ℝ)) (tA 13119 * 165 ^ 2 + 26 / (10 * 13119)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((899941 / 250000000))) * ((43232847 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((899941 / 250000000)) ^ 3) * ((1318175091 / 1000000000000000000000000))) + ((1970453857 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((899941 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13119) : ℝ)) d.D d.V d.P (√(tA 13119) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((899941 / 250000000)) ^ 2 * (((415850199 / 200000000000000)) * ((907667027 / 25000000000000000)))) + ((1970453857 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13119) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((899941 / 250000000)) * ((43232847 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13119) : ℝ)) (tA 13119 * 165 ^ 2 + 26 / (10 * 13119)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((43232847 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((899941 / 250000000)) ^ 2) * ((1318175091 / 1000000000000000000000000)) + ((1970453857 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13119) : ℝ)) (√(26 / (10 * 13119) : ℝ)) d.D d.V d.P (√(tA 13119) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((899941 / 250000000)) * (((415850199 / 200000000000000)) * ((907667027 / 25000000000000000))) + ((1970453857 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13119) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((43232847 / 10000000000000000000) : ℝ) + ((1970453857 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13119

namespace BstLean.Part266.Row13119
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13119 165 ∧
    0 ≤ (tableEnvelope C).f1 13119 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13119 165 ∧
    0 ≤ (tableEnvelope C).w1 13119 165 ∧ 0 ≤ (tableEnvelope C).w2 13119 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13119 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13119 165 ∧ 0 ≤ d.f1 13119 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13119 165 ∧ 0 ≤ d.w1 13119 165 ∧ 0 ≤ d.w2 13119 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13119 ≤ 2 * (228 / 100 : ℝ) / 13119 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13119 ≤ 2 * (370 / 100 : ℝ) / 13119 := by
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
    (completeRAData (tableEnvelope C) 13119 165).locationBound 13119 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13119 165).energyBound 13119 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13119 165) (d.f1 13119 165) d.f2 ≤
      32 * (((4225488769 / 1000000000000000000) : ℝ) + (281938903 / 200000000000000000) + (84705153 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13119 165) (d.w1 13119 165)
      (d.w2 13119 165) ≤
      32 * (((1663092599 / 100000000000000000000) : ℝ) + (1183258607 / 100000000000000000000) + (844399 / 195312500000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13119 165) (d.f1 13119 165) d.f2 ≤
      ((4225488769 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4225488769 / 1000000000000000000)) * ((281938903 / 200000000000000000)) * (126 / 100) +
      2 * (((281938903 / 200000000000000000)) ^ 2 + 2 * ((4225488769 / 1000000000000000000)) * ((84705153 / 250000000000000000))) +
      6 * ((281938903 / 200000000000000000)) * ((84705153 / 250000000000000000)) * (126 / 100) + 8 * ((84705153 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13119 165) (d.f1 13119 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13119 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13119 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13119 165) (d.f1 13119 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13119 165) (d.w1 13119 165) (d.w2 13119 165)
  have hwexpr0 : 0 ≤ d.w0 13119 165 + d.w1 13119 165 * √(π / 2) +
      2 * d.w2 13119 165 + energyR16 13119 *
      radiusPolynomialRoot16 (d.w0 13119 165) (d.w1 13119 165) (d.w2 13119 165) := by
    positivity
  constructor
  · change (13119 : ℝ) ^ 8 * (mA 13119 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13119 165) (d.f1 13119 165) d.f2 + locationR16 13119 *
        radiusPolynomialRoot16 (d.f0 13119 165) (d.f1 13119 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13119 : ℝ) ^ 8 * (mA 13119 : ℝ) ^ 8 *
        ((((4225488769 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4225488769 / 1000000000000000000)) * ((281938903 / 200000000000000000)) * (126 / 100) +
          2 * (((281938903 / 200000000000000000)) ^ 2 + 2 * ((4225488769 / 1000000000000000000)) * ((84705153 / 250000000000000000))) +
          6 * ((281938903 / 200000000000000000)) * ((84705153 / 250000000000000000)) * (126 / 100) + 8 * ((84705153 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13119) *
          (32 * (((4225488769 / 1000000000000000000) : ℝ) + (281938903 / 200000000000000000) + (84705153 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13119 : ℝ) ^ 16 *
      (d.w0 13119 165 + d.w1 13119 165 * √(π / 2) + 2 * d.w2 13119 165 +
        energyR16 13119 * radiusPolynomialRoot16 (d.w0 13119 165) (d.w1 13119 165)
          (d.w2 13119 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13119 : ℝ) ^ 16 *
        (((1663092599 / 100000000000000000000) : ℝ) + ((1183258607 / 100000000000000000000)) * (126 / 100) + 2 * ((844399 / 195312500000000000)) +
          (2 * (370 / 100 : ℝ) / 13119) *
          (32 * (((1663092599 / 100000000000000000000) : ℝ) + (1183258607 / 100000000000000000000) + (844399 / 195312500000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13119

/-! A coarse bound on the actual paper statistics constant at dimension 13120. -/
namespace BstLean.Part266.Row13120
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13118 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13118 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13118 128 ≤ (13372 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13372 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13120) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13120 : ℕ))
    (by norm_num : (13120 : ℕ) ≤ 16384)
  have ht : paperTail256 13120 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13120 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13120 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13120 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13120 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13120 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13118 128 * √(2 / (13120 : ℝ)) *
      (√(13120 : ℝ) + paperT0 13120 + paperTail256 13120) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13120 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13120 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13120 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13118 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13118 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13120 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13120

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13120
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13120 (61 / 100) 165 (17 / (100 * 13120)) (26 / (10 * 13120)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13120 (61 / 100) 165 (17 / (100 * 13120)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (27014351 / 6250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1317773239 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3938482899 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13120 / 13120 * (61 / 100)) ^ 4 * inverseRadius8 (13120 - 1) /
            envelopeGap 13120 (61 / 100) 165 (17 / (100 * 13120)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13120

namespace BstLean.Part266.Row13120
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13120 165 ≤ (1056170741 / 250000000000000000)
  f1 : (tableEnvelope C).f1 13120 165 ≤ (352356437 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (338756031 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13120 165 ≤ (831356099 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13120 165 ≤ (295746997 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 13120 165 ≤ (54029179 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (27014351 / 6250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (27014351 / 6250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1317773239 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3938482899 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3599627 / 1000000000) : ℝ) ≤ √(17 / (100 * 13120) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13120) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1039506633 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1452045861 / 40000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13120) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13120) ≤ (26947667 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13120) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13120 * (165 : ℝ) ^ 2 + 26 / (10 * 13120) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13120) : ℝ)) (tA 13120 * 165 ^ 2 + 26 / (10 * 13120)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3599627 / 1000000000))) * ((27014351 / 6250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3599627 / 1000000000)) ^ 3) * ((1317773239 / 1000000000000000000000000))) + ((3938482899 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3599627 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13120) : ℝ)) d.D d.V d.P (√(tA 13120) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3599627 / 1000000000)) ^ 2 * (((1039506633 / 500000000000000)) * ((1452045861 / 40000000000000000)))) + ((3938482899 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13120) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3599627 / 1000000000)) * ((27014351 / 6250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13120) : ℝ)) (tA 13120 * 165 ^ 2 + 26 / (10 * 13120)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((27014351 / 6250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3599627 / 1000000000)) ^ 2) * ((1317773239 / 1000000000000000000000000)) + ((3938482899 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13120) : ℝ)) (√(26 / (10 * 13120) : ℝ)) d.D d.V d.P (√(tA 13120) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3599627 / 1000000000)) * (((1039506633 / 500000000000000)) * ((1452045861 / 40000000000000000))) + ((3938482899 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13120) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((27014351 / 6250000000000000000) : ℝ) + ((3938482899 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13120

namespace BstLean.Part266.Row13120
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13120 165 ∧
    0 ≤ (tableEnvelope C).f1 13120 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13120 165 ∧
    0 ≤ (tableEnvelope C).w1 13120 165 ∧ 0 ≤ (tableEnvelope C).w2 13120 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13120 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13120 165 ∧ 0 ≤ d.f1 13120 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13120 165 ∧ 0 ≤ d.w1 13120 165 ∧ 0 ≤ d.w2 13120 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13120 ≤ 2 * (228 / 100 : ℝ) / 13120 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13120 ≤ 2 * (370 / 100 : ℝ) / 13120 := by
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
    (completeRAData (tableEnvelope C) 13120 165).locationBound 13120 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13120 165).energyBound 13120 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13120 165) (d.f1 13120 165) d.f2 ≤
      32 * (((1056170741 / 250000000000000000) : ℝ) + (352356437 / 250000000000000000) + (338756031 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13120 165) (d.w1 13120 165)
      (d.w2 13120 165) ≤
      32 * (((831356099 / 50000000000000000000) : ℝ) + (295746997 / 25000000000000000000) + (54029179 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13120 165) (d.f1 13120 165) d.f2 ≤
      ((1056170741 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1056170741 / 250000000000000000)) * ((352356437 / 250000000000000000)) * (126 / 100) +
      2 * (((352356437 / 250000000000000000)) ^ 2 + 2 * ((1056170741 / 250000000000000000)) * ((338756031 / 1000000000000000000))) +
      6 * ((352356437 / 250000000000000000)) * ((338756031 / 1000000000000000000)) * (126 / 100) + 8 * ((338756031 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13120 165) (d.f1 13120 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13120 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13120 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13120 165) (d.f1 13120 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13120 165) (d.w1 13120 165) (d.w2 13120 165)
  have hwexpr0 : 0 ≤ d.w0 13120 165 + d.w1 13120 165 * √(π / 2) +
      2 * d.w2 13120 165 + energyR16 13120 *
      radiusPolynomialRoot16 (d.w0 13120 165) (d.w1 13120 165) (d.w2 13120 165) := by
    positivity
  constructor
  · change (13120 : ℝ) ^ 8 * (mA 13120 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13120 165) (d.f1 13120 165) d.f2 + locationR16 13120 *
        radiusPolynomialRoot16 (d.f0 13120 165) (d.f1 13120 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13120 : ℝ) ^ 8 * (mA 13120 : ℝ) ^ 8 *
        ((((1056170741 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1056170741 / 250000000000000000)) * ((352356437 / 250000000000000000)) * (126 / 100) +
          2 * (((352356437 / 250000000000000000)) ^ 2 + 2 * ((1056170741 / 250000000000000000)) * ((338756031 / 1000000000000000000))) +
          6 * ((352356437 / 250000000000000000)) * ((338756031 / 1000000000000000000)) * (126 / 100) + 8 * ((338756031 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13120) *
          (32 * (((1056170741 / 250000000000000000) : ℝ) + (352356437 / 250000000000000000) + (338756031 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13120 : ℝ) ^ 16 *
      (d.w0 13120 165 + d.w1 13120 165 * √(π / 2) + 2 * d.w2 13120 165 +
        energyR16 13120 * radiusPolynomialRoot16 (d.w0 13120 165) (d.w1 13120 165)
          (d.w2 13120 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13120 : ℝ) ^ 16 *
        (((831356099 / 50000000000000000000) : ℝ) + ((295746997 / 25000000000000000000)) * (126 / 100) + 2 * ((54029179 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13120) *
          (32 * (((831356099 / 50000000000000000000) : ℝ) + (295746997 / 25000000000000000000) + (54029179 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13120

/-! A coarse bound on the actual paper statistics constant at dimension 13121. -/
namespace BstLean.Part266.Row13121
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13119 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13119 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13119 128 ≤ (13373 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13373 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13121) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13121 : ℕ))
    (by norm_num : (13121 : ℕ) ≤ 16384)
  have ht : paperTail256 13121 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13121 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13121 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13121 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13121 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13121 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13119 128 * √(2 / (13121 : ℝ)) *
      (√(13121 : ℝ) + paperT0 13121 + paperTail256 13121) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13121 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13121 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13121 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13119 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13119 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13121 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13121

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13121
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13121 (61 / 100) 165 (17 / (100 * 13121)) (26 / (10 * 13121)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13121 (61 / 100) 165 (17 / (100 * 13121)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (216065397 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (65868577 / 50000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (787211953 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13121 / 13121 * (61 / 100)) ^ 4 * inverseRadius8 (13121 - 1) /
            envelopeGap 13121 (61 / 100) 165 (17 / (100 * 13121)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13121

namespace BstLean.Part266.Row13121
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13121 165 ≤ (1055969357 / 250000000000000000)
  f1 : (tableEnvelope C).f1 13121 165 ≤ (140915707 / 100000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (338691471 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13121 165 ≤ (831165963 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13121 165 ≤ (1182717459 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13121 165 ≤ (432134607 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (216065397 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (216065397 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (65868577 / 50000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (787211953 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((359949 / 100000000) : ℝ) ≤ √(17 / (100 * 13121) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13121) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2078775587 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18147806617 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13121) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13121) ≤ (107782453 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13121) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13121 * (165 : ℝ) ^ 2 + 26 / (10 * 13121) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13121) : ℝ)) (tA 13121 * 165 ^ 2 + 26 / (10 * 13121)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((359949 / 100000000))) * ((216065397 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((359949 / 100000000)) ^ 3) * ((65868577 / 50000000000000000000000))) + ((787211953 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((359949 / 100000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13121) : ℝ)) d.D d.V d.P (√(tA 13121) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((359949 / 100000000)) ^ 2 * (((2078775587 / 1000000000000000)) * ((18147806617 / 500000000000000000)))) + ((787211953 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13121) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((359949 / 100000000)) * ((216065397 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13121) : ℝ)) (tA 13121 * 165 ^ 2 + 26 / (10 * 13121)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((216065397 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((359949 / 100000000)) ^ 2) * ((65868577 / 50000000000000000000000)) + ((787211953 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13121) : ℝ)) (√(26 / (10 * 13121) : ℝ)) d.D d.V d.P (√(tA 13121) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((359949 / 100000000)) * (((2078775587 / 1000000000000000)) * ((18147806617 / 500000000000000000))) + ((787211953 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13121) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((216065397 / 50000000000000000000) : ℝ) + ((787211953 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13121

namespace BstLean.Part266.Row13121
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13121 165 ∧
    0 ≤ (tableEnvelope C).f1 13121 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13121 165 ∧
    0 ≤ (tableEnvelope C).w1 13121 165 ∧ 0 ≤ (tableEnvelope C).w2 13121 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13121 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13121 165 ∧ 0 ≤ d.f1 13121 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13121 165 ∧ 0 ≤ d.w1 13121 165 ∧ 0 ≤ d.w2 13121 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13121 ≤ 2 * (228 / 100 : ℝ) / 13121 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13121 ≤ 2 * (370 / 100 : ℝ) / 13121 := by
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
    (completeRAData (tableEnvelope C) 13121 165).locationBound 13121 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13121 165).energyBound 13121 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13121 165) (d.f1 13121 165) d.f2 ≤
      32 * (((1055969357 / 250000000000000000) : ℝ) + (140915707 / 100000000000000000) + (338691471 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13121 165) (d.w1 13121 165)
      (d.w2 13121 165) ≤
      32 * (((831165963 / 50000000000000000000) : ℝ) + (1182717459 / 100000000000000000000) + (432134607 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13121 165) (d.f1 13121 165) d.f2 ≤
      ((1055969357 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1055969357 / 250000000000000000)) * ((140915707 / 100000000000000000)) * (126 / 100) +
      2 * (((140915707 / 100000000000000000)) ^ 2 + 2 * ((1055969357 / 250000000000000000)) * ((338691471 / 1000000000000000000))) +
      6 * ((140915707 / 100000000000000000)) * ((338691471 / 1000000000000000000)) * (126 / 100) + 8 * ((338691471 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13121 165) (d.f1 13121 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13121 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13121 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13121 165) (d.f1 13121 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13121 165) (d.w1 13121 165) (d.w2 13121 165)
  have hwexpr0 : 0 ≤ d.w0 13121 165 + d.w1 13121 165 * √(π / 2) +
      2 * d.w2 13121 165 + energyR16 13121 *
      radiusPolynomialRoot16 (d.w0 13121 165) (d.w1 13121 165) (d.w2 13121 165) := by
    positivity
  constructor
  · change (13121 : ℝ) ^ 8 * (mA 13121 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13121 165) (d.f1 13121 165) d.f2 + locationR16 13121 *
        radiusPolynomialRoot16 (d.f0 13121 165) (d.f1 13121 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13121 : ℝ) ^ 8 * (mA 13121 : ℝ) ^ 8 *
        ((((1055969357 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1055969357 / 250000000000000000)) * ((140915707 / 100000000000000000)) * (126 / 100) +
          2 * (((140915707 / 100000000000000000)) ^ 2 + 2 * ((1055969357 / 250000000000000000)) * ((338691471 / 1000000000000000000))) +
          6 * ((140915707 / 100000000000000000)) * ((338691471 / 1000000000000000000)) * (126 / 100) + 8 * ((338691471 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13121) *
          (32 * (((1055969357 / 250000000000000000) : ℝ) + (140915707 / 100000000000000000) + (338691471 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13121 : ℝ) ^ 16 *
      (d.w0 13121 165 + d.w1 13121 165 * √(π / 2) + 2 * d.w2 13121 165 +
        energyR16 13121 * radiusPolynomialRoot16 (d.w0 13121 165) (d.w1 13121 165)
          (d.w2 13121 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13121 : ℝ) ^ 16 *
        (((831165963 / 50000000000000000000) : ℝ) + ((1182717459 / 100000000000000000000)) * (126 / 100) + 2 * ((432134607 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13121) *
          (32 * (((831165963 / 50000000000000000000) : ℝ) + (1182717459 / 100000000000000000000) + (432134607 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13121

/-! A coarse bound on the actual paper statistics constant at dimension 13122. -/
namespace BstLean.Part266.Row13122
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13120 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13120 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13120 128 ≤ (13374 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13374 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13122) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13122 : ℕ))
    (by norm_num : (13122 : ℕ) ≤ 16384)
  have ht : paperTail256 13122 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13122 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13122 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13122 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13122 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13122 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13120 128 * √(2 / (13122 : ℝ)) *
      (√(13122 : ℝ) + paperT0 13122 + paperTail256 13122) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13122 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13122 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13122 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13120 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13120 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13122 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13122

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13122
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13122 (61 / 100) 165 (17 / (100 * 13122)) (26 / (10 * 13122)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13122 (61 / 100) 165 (17 / (100 * 13122)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (432032001 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (658484997 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3933638309 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13122 / 13122 * (61 / 100)) ^ 4 * inverseRadius8 (13122 - 1) /
            envelopeGap 13122 (61 / 100) 165 (17 / (100 * 13122)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13122

namespace BstLean.Part266.Row13122
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13122 165 ≤ (4223072159 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13122 165 ≤ (1408888473 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (21164183 / 62500000000000000)
  w0 : (tableEnvelope C).w0 13122 165 ≤ (1661951779 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13122 165 ≤ (1182447017 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13122 165 ≤ (108008953 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (432032001 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (432032001 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (658484997 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3933638309 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3599353 / 1000000000) : ℝ) ≤ √(17 / (100 * 13122) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13122) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2078537951 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36290081207 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13122) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13122) ≤ (107774239 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13122) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13122 * (165 : ℝ) ^ 2 + 26 / (10 * 13122) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13122) : ℝ)) (tA 13122 * 165 ^ 2 + 26 / (10 * 13122)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3599353 / 1000000000))) * ((432032001 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3599353 / 1000000000)) ^ 3) * ((658484997 / 500000000000000000000000))) + ((3933638309 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3599353 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13122) : ℝ)) d.D d.V d.P (√(tA 13122) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3599353 / 1000000000)) ^ 2 * (((2078537951 / 1000000000000000)) * ((36290081207 / 1000000000000000000)))) + ((3933638309 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13122) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3599353 / 1000000000)) * ((432032001 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13122) : ℝ)) (tA 13122 * 165 ^ 2 + 26 / (10 * 13122)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((432032001 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3599353 / 1000000000)) ^ 2) * ((658484997 / 500000000000000000000000)) + ((3933638309 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13122) : ℝ)) (√(26 / (10 * 13122) : ℝ)) d.D d.V d.P (√(tA 13122) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3599353 / 1000000000)) * (((2078537951 / 1000000000000000)) * ((36290081207 / 1000000000000000000))) + ((3933638309 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13122) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((432032001 / 100000000000000000000) : ℝ) + ((3933638309 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13122

namespace BstLean.Part266.Row13122
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13122 165 ∧
    0 ≤ (tableEnvelope C).f1 13122 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13122 165 ∧
    0 ≤ (tableEnvelope C).w1 13122 165 ∧ 0 ≤ (tableEnvelope C).w2 13122 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13122 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13122 165 ∧ 0 ≤ d.f1 13122 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13122 165 ∧ 0 ≤ d.w1 13122 165 ∧ 0 ≤ d.w2 13122 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13122 ≤ 2 * (228 / 100 : ℝ) / 13122 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13122 ≤ 2 * (370 / 100 : ℝ) / 13122 := by
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
    (completeRAData (tableEnvelope C) 13122 165).locationBound 13122 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13122 165).energyBound 13122 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13122 165) (d.f1 13122 165) d.f2 ≤
      32 * (((4223072159 / 1000000000000000000) : ℝ) + (1408888473 / 1000000000000000000) + (21164183 / 62500000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13122 165) (d.w1 13122 165)
      (d.w2 13122 165) ≤
      32 * (((1661951779 / 100000000000000000000) : ℝ) + (1182447017 / 100000000000000000000) + (108008953 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13122 165) (d.f1 13122 165) d.f2 ≤
      ((4223072159 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4223072159 / 1000000000000000000)) * ((1408888473 / 1000000000000000000)) * (126 / 100) +
      2 * (((1408888473 / 1000000000000000000)) ^ 2 + 2 * ((4223072159 / 1000000000000000000)) * ((21164183 / 62500000000000000))) +
      6 * ((1408888473 / 1000000000000000000)) * ((21164183 / 62500000000000000)) * (126 / 100) + 8 * ((21164183 / 62500000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13122 165) (d.f1 13122 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13122 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13122 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13122 165) (d.f1 13122 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13122 165) (d.w1 13122 165) (d.w2 13122 165)
  have hwexpr0 : 0 ≤ d.w0 13122 165 + d.w1 13122 165 * √(π / 2) +
      2 * d.w2 13122 165 + energyR16 13122 *
      radiusPolynomialRoot16 (d.w0 13122 165) (d.w1 13122 165) (d.w2 13122 165) := by
    positivity
  constructor
  · change (13122 : ℝ) ^ 8 * (mA 13122 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13122 165) (d.f1 13122 165) d.f2 + locationR16 13122 *
        radiusPolynomialRoot16 (d.f0 13122 165) (d.f1 13122 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13122 : ℝ) ^ 8 * (mA 13122 : ℝ) ^ 8 *
        ((((4223072159 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4223072159 / 1000000000000000000)) * ((1408888473 / 1000000000000000000)) * (126 / 100) +
          2 * (((1408888473 / 1000000000000000000)) ^ 2 + 2 * ((4223072159 / 1000000000000000000)) * ((21164183 / 62500000000000000))) +
          6 * ((1408888473 / 1000000000000000000)) * ((21164183 / 62500000000000000)) * (126 / 100) + 8 * ((21164183 / 62500000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13122) *
          (32 * (((4223072159 / 1000000000000000000) : ℝ) + (1408888473 / 1000000000000000000) + (21164183 / 62500000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13122 : ℝ) ^ 16 *
      (d.w0 13122 165 + d.w1 13122 165 * √(π / 2) + 2 * d.w2 13122 165 +
        energyR16 13122 * radiusPolynomialRoot16 (d.w0 13122 165) (d.w1 13122 165)
          (d.w2 13122 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13122 : ℝ) ^ 16 *
        (((1661951779 / 100000000000000000000) : ℝ) + ((1182447017 / 100000000000000000000)) * (126 / 100) + 2 * ((108008953 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13122) *
          (32 * (((1661951779 / 100000000000000000000) : ℝ) + (1182447017 / 100000000000000000000) + (108008953 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13122

/-! A coarse bound on the actual paper statistics constant at dimension 13123. -/
namespace BstLean.Part266.Row13123
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13121 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13121 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13121 128 ≤ (13375 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13375 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13123) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13123 : ℕ))
    (by norm_num : (13123 : ℕ) ≤ 16384)
  have ht : paperTail256 13123 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13123 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13123 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13123 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13123 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13123 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13121 128 * √(2 / (13123 : ℝ)) *
      (√(13123 : ℝ) + paperT0 13123 + paperTail256 13123) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13123 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13123 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13123 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13121 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13121 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13123 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13123

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13123
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13123 (61 / 100) 165 (17 / (100 * 13123)) (26 / (10 * 13123)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13123 (61 / 100) 165 (17 / (100 * 13123)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (215966619 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1316568601 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (393121853 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13123 / 13123 * (61 / 100)) ^ 4 * inverseRadius8 (13123 - 1) /
            envelopeGap 13123 (61 / 100) 165 (17 / (100 * 13123)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13123

namespace BstLean.Part266.Row13123
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13123 165 ≤ (263891909 / 62500000000000000)
  f1 : (tableEnvelope C).f1 13123 165 ≤ (704310371 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (169281249 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13123 165 ≤ (830786221 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13123 165 ≤ (118217699 / 10000000000000000000)
  w2 : (tableEnvelope C).w2 13123 165 ≤ (431937047 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (215966619 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (215966619 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1316568601 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (393121853 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((719843 / 200000000) : ℝ) ≤ √(17 / (100 * 13123) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13123) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2078300359 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18142275223 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13123) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13123) ≤ (107766027 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13123) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13123 * (165 : ℝ) ^ 2 + 26 / (10 * 13123) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13123) : ℝ)) (tA 13123 * 165 ^ 2 + 26 / (10 * 13123)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((719843 / 200000000))) * ((215966619 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((719843 / 200000000)) ^ 3) * ((1316568601 / 1000000000000000000000000))) + ((393121853 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((719843 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13123) : ℝ)) d.D d.V d.P (√(tA 13123) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((719843 / 200000000)) ^ 2 * (((2078300359 / 1000000000000000)) * ((18142275223 / 500000000000000000)))) + ((393121853 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13123) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((719843 / 200000000)) * ((215966619 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13123) : ℝ)) (tA 13123 * 165 ^ 2 + 26 / (10 * 13123)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((215966619 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((719843 / 200000000)) ^ 2) * ((1316568601 / 1000000000000000000000000)) + ((393121853 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13123) : ℝ)) (√(26 / (10 * 13123) : ℝ)) d.D d.V d.P (√(tA 13123) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((719843 / 200000000)) * (((2078300359 / 1000000000000000)) * ((18142275223 / 500000000000000000))) + ((393121853 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13123) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((215966619 / 50000000000000000000) : ℝ) + ((393121853 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13123

namespace BstLean.Part266.Row13123
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13123 165 ∧
    0 ≤ (tableEnvelope C).f1 13123 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13123 165 ∧
    0 ≤ (tableEnvelope C).w1 13123 165 ∧ 0 ≤ (tableEnvelope C).w2 13123 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13123 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13123 165 ∧ 0 ≤ d.f1 13123 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13123 165 ∧ 0 ≤ d.w1 13123 165 ∧ 0 ≤ d.w2 13123 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13123 ≤ 2 * (228 / 100 : ℝ) / 13123 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13123 ≤ 2 * (370 / 100 : ℝ) / 13123 := by
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
    (completeRAData (tableEnvelope C) 13123 165).locationBound 13123 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13123 165).energyBound 13123 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13123 165) (d.f1 13123 165) d.f2 ≤
      32 * (((263891909 / 62500000000000000) : ℝ) + (704310371 / 500000000000000000) + (169281249 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13123 165) (d.w1 13123 165)
      (d.w2 13123 165) ≤
      32 * (((830786221 / 50000000000000000000) : ℝ) + (118217699 / 10000000000000000000) + (431937047 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13123 165) (d.f1 13123 165) d.f2 ≤
      ((263891909 / 62500000000000000) : ℝ) ^ 2 + 2 * ((263891909 / 62500000000000000)) * ((704310371 / 500000000000000000)) * (126 / 100) +
      2 * (((704310371 / 500000000000000000)) ^ 2 + 2 * ((263891909 / 62500000000000000)) * ((169281249 / 500000000000000000))) +
      6 * ((704310371 / 500000000000000000)) * ((169281249 / 500000000000000000)) * (126 / 100) + 8 * ((169281249 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13123 165) (d.f1 13123 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13123 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13123 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13123 165) (d.f1 13123 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13123 165) (d.w1 13123 165) (d.w2 13123 165)
  have hwexpr0 : 0 ≤ d.w0 13123 165 + d.w1 13123 165 * √(π / 2) +
      2 * d.w2 13123 165 + energyR16 13123 *
      radiusPolynomialRoot16 (d.w0 13123 165) (d.w1 13123 165) (d.w2 13123 165) := by
    positivity
  constructor
  · change (13123 : ℝ) ^ 8 * (mA 13123 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13123 165) (d.f1 13123 165) d.f2 + locationR16 13123 *
        radiusPolynomialRoot16 (d.f0 13123 165) (d.f1 13123 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13123 : ℝ) ^ 8 * (mA 13123 : ℝ) ^ 8 *
        ((((263891909 / 62500000000000000) : ℝ) ^ 2 + 2 * ((263891909 / 62500000000000000)) * ((704310371 / 500000000000000000)) * (126 / 100) +
          2 * (((704310371 / 500000000000000000)) ^ 2 + 2 * ((263891909 / 62500000000000000)) * ((169281249 / 500000000000000000))) +
          6 * ((704310371 / 500000000000000000)) * ((169281249 / 500000000000000000)) * (126 / 100) + 8 * ((169281249 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13123) *
          (32 * (((263891909 / 62500000000000000) : ℝ) + (704310371 / 500000000000000000) + (169281249 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13123 : ℝ) ^ 16 *
      (d.w0 13123 165 + d.w1 13123 165 * √(π / 2) + 2 * d.w2 13123 165 +
        energyR16 13123 * radiusPolynomialRoot16 (d.w0 13123 165) (d.w1 13123 165)
          (d.w2 13123 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13123 : ℝ) ^ 16 *
        (((830786221 / 50000000000000000000) : ℝ) + ((118217699 / 10000000000000000000)) * (126 / 100) + 2 * ((431937047 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13123) *
          (32 * (((830786221 / 50000000000000000000) : ℝ) + (118217699 / 10000000000000000000) + (431937047 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13123

/-! A coarse bound on the actual paper statistics constant at dimension 13124. -/
namespace BstLean.Part266.Row13124
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13122 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13122 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13122 128 ≤ (13376 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13376 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13124) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13124 : ℕ))
    (by norm_num : (13124 : ℕ) ≤ 16384)
  have ht : paperTail256 13124 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13124 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13124 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13124 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13124 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13124 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13122 128 * √(2 / (13124 : ℝ)) *
      (√(13124 : ℝ) + paperT0 13124 + paperTail256 13124) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13124 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13124 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13124 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13122 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13122 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13124 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13124

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13124
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13124 (61 / 100) 165 (17 / (100 * 13124)) (26 / (10 * 13124)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13124 (61 / 100) 165 (17 / (100 * 13124)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (86366901 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1316167361 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (982200107 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13124 / 13124 * (61 / 100)) ^ 4 * inverseRadius8 (13124 - 1) /
            envelopeGap 13124 (61 / 100) 165 (17 / (100 * 13124)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13124

namespace BstLean.Part266.Row13124
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13124 165 ≤ (4221465811 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13124 165 ≤ (176044039 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (338497993 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13124 165 ≤ (415298137 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 13124 165 ≤ (590953361 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13124 165 ≤ (431838311 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (86366901 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (86366901 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1316167361 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (982200107 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1799539 / 500000000) : ℝ) ≤ √(17 / (100 * 13124) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13124) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (519515703 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36279020949 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13124) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13124) ≤ (21551563 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13124) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13124 * (165 : ℝ) ^ 2 + 26 / (10 * 13124) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13124) : ℝ)) (tA 13124 * 165 ^ 2 + 26 / (10 * 13124)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1799539 / 500000000))) * ((86366901 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1799539 / 500000000)) ^ 3) * ((1316167361 / 1000000000000000000000000))) + ((982200107 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1799539 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13124) : ℝ)) d.D d.V d.P (√(tA 13124) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1799539 / 500000000)) ^ 2 * (((519515703 / 250000000000000)) * ((36279020949 / 1000000000000000000)))) + ((982200107 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13124) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1799539 / 500000000)) * ((86366901 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13124) : ℝ)) (tA 13124 * 165 ^ 2 + 26 / (10 * 13124)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((86366901 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1799539 / 500000000)) ^ 2) * ((1316167361 / 1000000000000000000000000)) + ((982200107 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13124) : ℝ)) (√(26 / (10 * 13124) : ℝ)) d.D d.V d.P (√(tA 13124) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1799539 / 500000000)) * (((519515703 / 250000000000000)) * ((36279020949 / 1000000000000000000))) + ((982200107 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13124) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((86366901 / 20000000000000000000) : ℝ) + ((982200107 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13124

namespace BstLean.Part266.Row13124
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13124 165 ∧
    0 ≤ (tableEnvelope C).f1 13124 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13124 165 ∧
    0 ≤ (tableEnvelope C).w1 13124 165 ∧ 0 ≤ (tableEnvelope C).w2 13124 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13124 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13124 165 ∧ 0 ≤ d.f1 13124 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13124 165 ∧ 0 ≤ d.w1 13124 165 ∧ 0 ≤ d.w2 13124 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13124 ≤ 2 * (228 / 100 : ℝ) / 13124 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13124 ≤ 2 * (370 / 100 : ℝ) / 13124 := by
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
    (completeRAData (tableEnvelope C) 13124 165).locationBound 13124 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13124 165).energyBound 13124 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13124 165) (d.f1 13124 165) d.f2 ≤
      32 * (((4221465811 / 1000000000000000000) : ℝ) + (176044039 / 125000000000000000) + (338497993 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13124 165) (d.w1 13124 165)
      (d.w2 13124 165) ≤
      32 * (((415298137 / 25000000000000000000) : ℝ) + (590953361 / 50000000000000000000) + (431838311 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13124 165) (d.f1 13124 165) d.f2 ≤
      ((4221465811 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4221465811 / 1000000000000000000)) * ((176044039 / 125000000000000000)) * (126 / 100) +
      2 * (((176044039 / 125000000000000000)) ^ 2 + 2 * ((4221465811 / 1000000000000000000)) * ((338497993 / 1000000000000000000))) +
      6 * ((176044039 / 125000000000000000)) * ((338497993 / 1000000000000000000)) * (126 / 100) + 8 * ((338497993 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13124 165) (d.f1 13124 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13124 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13124 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13124 165) (d.f1 13124 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13124 165) (d.w1 13124 165) (d.w2 13124 165)
  have hwexpr0 : 0 ≤ d.w0 13124 165 + d.w1 13124 165 * √(π / 2) +
      2 * d.w2 13124 165 + energyR16 13124 *
      radiusPolynomialRoot16 (d.w0 13124 165) (d.w1 13124 165) (d.w2 13124 165) := by
    positivity
  constructor
  · change (13124 : ℝ) ^ 8 * (mA 13124 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13124 165) (d.f1 13124 165) d.f2 + locationR16 13124 *
        radiusPolynomialRoot16 (d.f0 13124 165) (d.f1 13124 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13124 : ℝ) ^ 8 * (mA 13124 : ℝ) ^ 8 *
        ((((4221465811 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4221465811 / 1000000000000000000)) * ((176044039 / 125000000000000000)) * (126 / 100) +
          2 * (((176044039 / 125000000000000000)) ^ 2 + 2 * ((4221465811 / 1000000000000000000)) * ((338497993 / 1000000000000000000))) +
          6 * ((176044039 / 125000000000000000)) * ((338497993 / 1000000000000000000)) * (126 / 100) + 8 * ((338497993 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13124) *
          (32 * (((4221465811 / 1000000000000000000) : ℝ) + (176044039 / 125000000000000000) + (338497993 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13124 : ℝ) ^ 16 *
      (d.w0 13124 165 + d.w1 13124 165 * √(π / 2) + 2 * d.w2 13124 165 +
        energyR16 13124 * radiusPolynomialRoot16 (d.w0 13124 165) (d.w1 13124 165)
          (d.w2 13124 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13124 : ℝ) ^ 16 *
        (((415298137 / 25000000000000000000) : ℝ) + ((590953361 / 50000000000000000000)) * (126 / 100) + 2 * ((431838311 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13124) *
          (32 * (((415298137 / 25000000000000000000) : ℝ) + (590953361 / 50000000000000000000) + (431838311 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13124
