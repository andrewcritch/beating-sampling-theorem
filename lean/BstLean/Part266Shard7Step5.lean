import BstLean.Part266Shard7Step4


/-! A coarse bound on the actual paper statistics constant at dimension 12525. -/
namespace BstLean.Part266.Row12525
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12523 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12523 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12523 128 ≤ (12777 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12777 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12525) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12525 : ℕ))
    (by norm_num : (12525 : ℕ) ≤ 16384)
  have ht : paperTail256 12525 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12525 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12525 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12525 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12525 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12525 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12523 128 * √(2 / (12525 : ℝ)) *
      (√(12525 : ℝ) + paperT0 12525 + paperTail256 12525) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12525 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12525 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12525 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12523 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12523 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12525 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12525

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12525
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12525 (61 / 100) 162 (17 / (100 * 12525)) (26 / (10 * 12525)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12525 (61 / 100) 162 (17 / (100 * 12525)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (124201253 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (198325357 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (572177381 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12525 / 12525 * (61 / 100)) ^ 4 * inverseRadius8 (12525 - 1) /
            envelopeGap 12525 (61 / 100) 162 (17 / (100 * 12525)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12525

namespace BstLean.Part266.Row12525
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12525 162 ≤ (4744468569 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12525 162 ≤ (1582835077 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (76086997 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12525 162 ≤ (1911122887 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12525 162 ≤ (1359727421 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12525 162 ≤ (99362111 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (124201253 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (124201253 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (198325357 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (572177381 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((736827 / 200000000) : ℝ) ≤ √(17 / (100 * 12525) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12525) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1114456159 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39832183671 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12525) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12525) ≤ (112911263 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12525) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12525 * (162 : ℝ) ^ 2 + 26 / (10 * 12525) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12525) : ℝ)) (tA 12525 * 162 ^ 2 + 26 / (10 * 12525)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((736827 / 200000000))) * ((124201253 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((736827 / 200000000)) ^ 3) * ((198325357 / 125000000000000000000000))) + ((572177381 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((736827 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12525) : ℝ)) d.D d.V d.P (√(tA 12525) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((736827 / 200000000)) ^ 2 * (((1114456159 / 500000000000000)) * ((39832183671 / 1000000000000000000)))) + ((572177381 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12525) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((736827 / 200000000)) * ((124201253 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12525) : ℝ)) (tA 12525 * 162 ^ 2 + 26 / (10 * 12525)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((124201253 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((736827 / 200000000)) ^ 2) * ((198325357 / 125000000000000000000000)) + ((572177381 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12525) : ℝ)) (√(26 / (10 * 12525) : ℝ)) d.D d.V d.P (√(tA 12525) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((736827 / 200000000)) * (((1114456159 / 500000000000000)) * ((39832183671 / 1000000000000000000))) + ((572177381 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12525) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((124201253 / 25000000000000000000) : ℝ) + ((572177381 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12525

namespace BstLean.Part266.Row12525
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12525 162 ∧
    0 ≤ (tableEnvelope C).f1 12525 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12525 162 ∧
    0 ≤ (tableEnvelope C).w1 12525 162 ∧ 0 ≤ (tableEnvelope C).w2 12525 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12525 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12525 162 ∧ 0 ≤ d.f1 12525 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12525 162 ∧ 0 ≤ d.w1 12525 162 ∧ 0 ≤ d.w2 12525 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12525 ≤ 2 * (228 / 100 : ℝ) / 12525 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12525 ≤ 2 * (370 / 100 : ℝ) / 12525 := by
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
    (completeRAData (tableEnvelope C) 12525 162).locationBound 12525 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12525 162).energyBound 12525 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12525 162) (d.f1 12525 162) d.f2 ≤
      32 * (((4744468569 / 1000000000000000000) : ℝ) + (1582835077 / 1000000000000000000) + (76086997 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12525 162) (d.w1 12525 162)
      (d.w2 12525 162) ≤
      32 * (((1911122887 / 100000000000000000000) : ℝ) + (1359727421 / 100000000000000000000) + (99362111 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12525 162) (d.f1 12525 162) d.f2 ≤
      ((4744468569 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4744468569 / 1000000000000000000)) * ((1582835077 / 1000000000000000000)) * (126 / 100) +
      2 * (((1582835077 / 1000000000000000000)) ^ 2 + 2 * ((4744468569 / 1000000000000000000)) * ((76086997 / 200000000000000000))) +
      6 * ((1582835077 / 1000000000000000000)) * ((76086997 / 200000000000000000)) * (126 / 100) + 8 * ((76086997 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12525 162) (d.f1 12525 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12525 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12525 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12525 162) (d.f1 12525 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12525 162) (d.w1 12525 162) (d.w2 12525 162)
  have hwexpr0 : 0 ≤ d.w0 12525 162 + d.w1 12525 162 * √(π / 2) +
      2 * d.w2 12525 162 + energyR16 12525 *
      radiusPolynomialRoot16 (d.w0 12525 162) (d.w1 12525 162) (d.w2 12525 162) := by
    positivity
  constructor
  · change (12525 : ℝ) ^ 8 * (mA 12525 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12525 162) (d.f1 12525 162) d.f2 + locationR16 12525 *
        radiusPolynomialRoot16 (d.f0 12525 162) (d.f1 12525 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12525 : ℝ) ^ 8 * (mA 12525 : ℝ) ^ 8 *
        ((((4744468569 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4744468569 / 1000000000000000000)) * ((1582835077 / 1000000000000000000)) * (126 / 100) +
          2 * (((1582835077 / 1000000000000000000)) ^ 2 + 2 * ((4744468569 / 1000000000000000000)) * ((76086997 / 200000000000000000))) +
          6 * ((1582835077 / 1000000000000000000)) * ((76086997 / 200000000000000000)) * (126 / 100) + 8 * ((76086997 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12525) *
          (32 * (((4744468569 / 1000000000000000000) : ℝ) + (1582835077 / 1000000000000000000) + (76086997 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12525 : ℝ) ^ 16 *
      (d.w0 12525 162 + d.w1 12525 162 * √(π / 2) + 2 * d.w2 12525 162 +
        energyR16 12525 * radiusPolynomialRoot16 (d.w0 12525 162) (d.w1 12525 162)
          (d.w2 12525 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12525 : ℝ) ^ 16 *
        (((1911122887 / 100000000000000000000) : ℝ) + ((1359727421 / 100000000000000000000)) * (126 / 100) + 2 * ((99362111 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12525) *
          (32 * (((1911122887 / 100000000000000000000) : ℝ) + (1359727421 / 100000000000000000000) + (99362111 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12525

/-! A coarse bound on the actual paper statistics constant at dimension 12526. -/
namespace BstLean.Part266.Row12526
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12524 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12524 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12524 128 ≤ (12778 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12778 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12526) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12526 : ℕ))
    (by norm_num : (12526 : ℕ) ≤ 16384)
  have ht : paperTail256 12526 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12526 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12526 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12526 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12526 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12526 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12524 128 * √(2 / (12526 : ℝ)) *
      (√(12526 : ℝ) + paperT0 12526 + paperTail256 12526) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12526 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12526 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12526 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12524 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12524 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12526 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12526

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12526
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12526 (61 / 100) 162 (17 / (100 * 12526)) (26 / (10 * 12526)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12526 (61 / 100) 162 (17 / (100 * 12526)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (496686029 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1586096237 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5718084369 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12526 / 12526 * (61 / 100)) ^ 4 * inverseRadius8 (12526 - 1) /
            envelopeGap 12526 (61 / 100) 162 (17 / (100 * 12526)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12526

namespace BstLean.Part266.Row12526
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12526 162 ≤ (37058761 / 7812500000000000)
  f1 : (tableEnvelope C).f1 12526 162 ≤ (1582519111 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (380359049 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12526 162 ≤ (1910665133 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12526 162 ≤ (1359401749 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12526 162 ≤ (496691569 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (496686029 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (496686029 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1586096237 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5718084369 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((920997 / 250000000) : ℝ) ≤ √(17 / (100 * 12526) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12526) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1114322697 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19912911873 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12526) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12526) ≤ (112902249 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12526) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12526 * (162 : ℝ) ^ 2 + 26 / (10 * 12526) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12526) : ℝ)) (tA 12526 * 162 ^ 2 + 26 / (10 * 12526)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((920997 / 250000000))) * ((496686029 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((920997 / 250000000)) ^ 3) * ((1586096237 / 1000000000000000000000000))) + ((5718084369 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((920997 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12526) : ℝ)) d.D d.V d.P (√(tA 12526) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((920997 / 250000000)) ^ 2 * (((1114322697 / 500000000000000)) * ((19912911873 / 500000000000000000)))) + ((5718084369 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12526) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((920997 / 250000000)) * ((496686029 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12526) : ℝ)) (tA 12526 * 162 ^ 2 + 26 / (10 * 12526)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((496686029 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((920997 / 250000000)) ^ 2) * ((1586096237 / 1000000000000000000000000)) + ((5718084369 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12526) : ℝ)) (√(26 / (10 * 12526) : ℝ)) d.D d.V d.P (√(tA 12526) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((920997 / 250000000)) * (((1114322697 / 500000000000000)) * ((19912911873 / 500000000000000000))) + ((5718084369 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12526) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((496686029 / 100000000000000000000) : ℝ) + ((5718084369 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12526

namespace BstLean.Part266.Row12526
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12526 162 ∧
    0 ≤ (tableEnvelope C).f1 12526 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12526 162 ∧
    0 ≤ (tableEnvelope C).w1 12526 162 ∧ 0 ≤ (tableEnvelope C).w2 12526 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12526 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12526 162 ∧ 0 ≤ d.f1 12526 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12526 162 ∧ 0 ≤ d.w1 12526 162 ∧ 0 ≤ d.w2 12526 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12526 ≤ 2 * (228 / 100 : ℝ) / 12526 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12526 ≤ 2 * (370 / 100 : ℝ) / 12526 := by
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
    (completeRAData (tableEnvelope C) 12526 162).locationBound 12526 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12526 162).energyBound 12526 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12526 162) (d.f1 12526 162) d.f2 ≤
      32 * (((37058761 / 7812500000000000) : ℝ) + (1582519111 / 1000000000000000000) + (380359049 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12526 162) (d.w1 12526 162)
      (d.w2 12526 162) ≤
      32 * (((1910665133 / 100000000000000000000) : ℝ) + (1359401749 / 100000000000000000000) + (496691569 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12526 162) (d.f1 12526 162) d.f2 ≤
      ((37058761 / 7812500000000000) : ℝ) ^ 2 + 2 * ((37058761 / 7812500000000000)) * ((1582519111 / 1000000000000000000)) * (126 / 100) +
      2 * (((1582519111 / 1000000000000000000)) ^ 2 + 2 * ((37058761 / 7812500000000000)) * ((380359049 / 1000000000000000000))) +
      6 * ((1582519111 / 1000000000000000000)) * ((380359049 / 1000000000000000000)) * (126 / 100) + 8 * ((380359049 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12526 162) (d.f1 12526 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12526 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12526 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12526 162) (d.f1 12526 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12526 162) (d.w1 12526 162) (d.w2 12526 162)
  have hwexpr0 : 0 ≤ d.w0 12526 162 + d.w1 12526 162 * √(π / 2) +
      2 * d.w2 12526 162 + energyR16 12526 *
      radiusPolynomialRoot16 (d.w0 12526 162) (d.w1 12526 162) (d.w2 12526 162) := by
    positivity
  constructor
  · change (12526 : ℝ) ^ 8 * (mA 12526 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12526 162) (d.f1 12526 162) d.f2 + locationR16 12526 *
        radiusPolynomialRoot16 (d.f0 12526 162) (d.f1 12526 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12526 : ℝ) ^ 8 * (mA 12526 : ℝ) ^ 8 *
        ((((37058761 / 7812500000000000) : ℝ) ^ 2 + 2 * ((37058761 / 7812500000000000)) * ((1582519111 / 1000000000000000000)) * (126 / 100) +
          2 * (((1582519111 / 1000000000000000000)) ^ 2 + 2 * ((37058761 / 7812500000000000)) * ((380359049 / 1000000000000000000))) +
          6 * ((1582519111 / 1000000000000000000)) * ((380359049 / 1000000000000000000)) * (126 / 100) + 8 * ((380359049 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12526) *
          (32 * (((37058761 / 7812500000000000) : ℝ) + (1582519111 / 1000000000000000000) + (380359049 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12526 : ℝ) ^ 16 *
      (d.w0 12526 162 + d.w1 12526 162 * √(π / 2) + 2 * d.w2 12526 162 +
        energyR16 12526 * radiusPolynomialRoot16 (d.w0 12526 162) (d.w1 12526 162)
          (d.w2 12526 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12526 : ℝ) ^ 16 *
        (((1910665133 / 100000000000000000000) : ℝ) + ((1359401749 / 100000000000000000000)) * (126 / 100) + 2 * ((496691569 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12526) *
          (32 * (((1910665133 / 100000000000000000000) : ℝ) + (1359401749 / 100000000000000000000) + (496691569 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12526

/-! A coarse bound on the actual paper statistics constant at dimension 12527. -/
namespace BstLean.Part266.Row12527
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12525 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12525 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12525 128 ≤ (12779 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12779 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12527) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12527 : ℕ))
    (by norm_num : (12527 : ℕ) ≤ 16384)
  have ht : paperTail256 12527 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12527 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12527 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12527 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12527 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12527 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12525 128 * √(2 / (12527 : ℝ)) *
      (√(12527 : ℝ) + paperT0 12527 + paperTail256 12527) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12527 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12527 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12527 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12525 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12525 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12527 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12527

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12527
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12527 (61 / 100) 162 (17 / (100 * 12527)) (26 / (10 * 12527)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12527 (61 / 100) 162 (17 / (100 * 12527)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (99313417 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1585589821 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (714299701 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12527 / 12527 * (61 / 100)) ^ 4 * inverseRadius8 (12527 - 1) /
            envelopeGap 12527 (61 / 100) 162 (17 / (100 * 12527)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12527

namespace BstLean.Part266.Row12527
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12527 162 ≤ (4742574579 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12527 162 ≤ (6328813 / 4000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (380283137 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12527 162 ≤ (1910207539 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12527 162 ≤ (339769047 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12527 162 ≤ (496572621 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (99313417 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (99313417 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1585589821 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (714299701 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3683841 / 1000000000) : ℝ) ≤ √(17 / (100 * 12527) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12527) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (89135141 / 40000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19909732677 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12527) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12527) ≤ (28223309 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12527) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12527 * (162 : ℝ) ^ 2 + 26 / (10 * 12527) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12527) : ℝ)) (tA 12527 * 162 ^ 2 + 26 / (10 * 12527)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3683841 / 1000000000))) * ((99313417 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3683841 / 1000000000)) ^ 3) * ((1585589821 / 1000000000000000000000000))) + ((714299701 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3683841 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12527) : ℝ)) d.D d.V d.P (√(tA 12527) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3683841 / 1000000000)) ^ 2 * (((89135141 / 40000000000000)) * ((19909732677 / 500000000000000000)))) + ((714299701 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12527) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3683841 / 1000000000)) * ((99313417 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12527) : ℝ)) (tA 12527 * 162 ^ 2 + 26 / (10 * 12527)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((99313417 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3683841 / 1000000000)) ^ 2) * ((1585589821 / 1000000000000000000000000)) + ((714299701 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12527) : ℝ)) (√(26 / (10 * 12527) : ℝ)) d.D d.V d.P (√(tA 12527) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3683841 / 1000000000)) * (((89135141 / 40000000000000)) * ((19909732677 / 500000000000000000))) + ((714299701 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12527) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((99313417 / 20000000000000000000) : ℝ) + ((714299701 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12527

namespace BstLean.Part266.Row12527
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12527 162 ∧
    0 ≤ (tableEnvelope C).f1 12527 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12527 162 ∧
    0 ≤ (tableEnvelope C).w1 12527 162 ∧ 0 ≤ (tableEnvelope C).w2 12527 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12527 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12527 162 ∧ 0 ≤ d.f1 12527 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12527 162 ∧ 0 ≤ d.w1 12527 162 ∧ 0 ≤ d.w2 12527 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12527 ≤ 2 * (228 / 100 : ℝ) / 12527 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12527 ≤ 2 * (370 / 100 : ℝ) / 12527 := by
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
    (completeRAData (tableEnvelope C) 12527 162).locationBound 12527 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12527 162).energyBound 12527 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12527 162) (d.f1 12527 162) d.f2 ≤
      32 * (((4742574579 / 1000000000000000000) : ℝ) + (6328813 / 4000000000000000) + (380283137 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12527 162) (d.w1 12527 162)
      (d.w2 12527 162) ≤
      32 * (((1910207539 / 100000000000000000000) : ℝ) + (339769047 / 25000000000000000000) + (496572621 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12527 162) (d.f1 12527 162) d.f2 ≤
      ((4742574579 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4742574579 / 1000000000000000000)) * ((6328813 / 4000000000000000)) * (126 / 100) +
      2 * (((6328813 / 4000000000000000)) ^ 2 + 2 * ((4742574579 / 1000000000000000000)) * ((380283137 / 1000000000000000000))) +
      6 * ((6328813 / 4000000000000000)) * ((380283137 / 1000000000000000000)) * (126 / 100) + 8 * ((380283137 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12527 162) (d.f1 12527 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12527 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12527 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12527 162) (d.f1 12527 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12527 162) (d.w1 12527 162) (d.w2 12527 162)
  have hwexpr0 : 0 ≤ d.w0 12527 162 + d.w1 12527 162 * √(π / 2) +
      2 * d.w2 12527 162 + energyR16 12527 *
      radiusPolynomialRoot16 (d.w0 12527 162) (d.w1 12527 162) (d.w2 12527 162) := by
    positivity
  constructor
  · change (12527 : ℝ) ^ 8 * (mA 12527 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12527 162) (d.f1 12527 162) d.f2 + locationR16 12527 *
        radiusPolynomialRoot16 (d.f0 12527 162) (d.f1 12527 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12527 : ℝ) ^ 8 * (mA 12527 : ℝ) ^ 8 *
        ((((4742574579 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4742574579 / 1000000000000000000)) * ((6328813 / 4000000000000000)) * (126 / 100) +
          2 * (((6328813 / 4000000000000000)) ^ 2 + 2 * ((4742574579 / 1000000000000000000)) * ((380283137 / 1000000000000000000))) +
          6 * ((6328813 / 4000000000000000)) * ((380283137 / 1000000000000000000)) * (126 / 100) + 8 * ((380283137 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12527) *
          (32 * (((4742574579 / 1000000000000000000) : ℝ) + (6328813 / 4000000000000000) + (380283137 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12527 : ℝ) ^ 16 *
      (d.w0 12527 162 + d.w1 12527 162 * √(π / 2) + 2 * d.w2 12527 162 +
        energyR16 12527 * radiusPolynomialRoot16 (d.w0 12527 162) (d.w1 12527 162)
          (d.w2 12527 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12527 : ℝ) ^ 16 *
        (((1910207539 / 100000000000000000000) : ℝ) + ((339769047 / 25000000000000000000)) * (126 / 100) + 2 * ((496572621 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12527) *
          (32 * (((1910207539 / 100000000000000000000) : ℝ) + (339769047 / 25000000000000000000) + (496572621 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12527

/-! A coarse bound on the actual paper statistics constant at dimension 12528. -/
namespace BstLean.Part266.Row12528
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12526 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12526 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12526 128 ≤ (12780 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12780 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12528) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12528 : ℕ))
    (by norm_num : (12528 : ℕ) ≤ 16384)
  have ht : paperTail256 12528 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12528 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12528 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12528 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12528 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12528 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12526 128 * √(2 / (12528 : ℝ)) *
      (√(12528 : ℝ) + paperT0 12528 + paperTail256 12528) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12528 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12528 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12528 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12526 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12526 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12528 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12528

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12528
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12528 (61 / 100) 162 (17 / (100 * 12528)) (26 / (10 * 12528)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12528 (61 / 100) 162 (17 / (100 * 12528)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (248224089 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1585083607 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5710713523 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12528 / 12528 * (61 / 100)) ^ 4 * inverseRadius8 (12528 - 1) /
            envelopeGap 12528 (61 / 100) 162 (17 / (100 * 12528)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12528

namespace BstLean.Part266.Row12528
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12528 162 ≤ (59270351 / 12500000000000000)
  f1 : (tableEnvelope C).f1 12528 162 ≤ (395471873 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (380207247 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12528 162 ≤ (381950021 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12528 162 ≤ (1358750737 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12528 162 ≤ (49645371 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (248224089 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (248224089 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1585083607 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5710713523 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1841847 / 500000000) : ℝ) ≤ √(17 / (100 * 12528) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12528) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (557027927 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39813108483 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12528) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12528) ≤ (4515369 / 40000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12528) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12528 * (162 : ℝ) ^ 2 + 26 / (10 * 12528) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12528) : ℝ)) (tA 12528 * 162 ^ 2 + 26 / (10 * 12528)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1841847 / 500000000))) * ((248224089 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1841847 / 500000000)) ^ 3) * ((1585083607 / 1000000000000000000000000))) + ((5710713523 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1841847 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12528) : ℝ)) d.D d.V d.P (√(tA 12528) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1841847 / 500000000)) ^ 2 * (((557027927 / 250000000000000)) * ((39813108483 / 1000000000000000000)))) + ((5710713523 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12528) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1841847 / 500000000)) * ((248224089 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12528) : ℝ)) (tA 12528 * 162 ^ 2 + 26 / (10 * 12528)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((248224089 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1841847 / 500000000)) ^ 2) * ((1585083607 / 1000000000000000000000000)) + ((5710713523 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12528) : ℝ)) (√(26 / (10 * 12528) : ℝ)) d.D d.V d.P (√(tA 12528) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1841847 / 500000000)) * (((557027927 / 250000000000000)) * ((39813108483 / 1000000000000000000))) + ((5710713523 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12528) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((248224089 / 50000000000000000000) : ℝ) + ((5710713523 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12528

namespace BstLean.Part266.Row12528
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12528 162 ∧
    0 ≤ (tableEnvelope C).f1 12528 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12528 162 ∧
    0 ≤ (tableEnvelope C).w1 12528 162 ∧ 0 ≤ (tableEnvelope C).w2 12528 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12528 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12528 162 ∧ 0 ≤ d.f1 12528 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12528 162 ∧ 0 ≤ d.w1 12528 162 ∧ 0 ≤ d.w2 12528 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12528 ≤ 2 * (228 / 100 : ℝ) / 12528 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12528 ≤ 2 * (370 / 100 : ℝ) / 12528 := by
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
    (completeRAData (tableEnvelope C) 12528 162).locationBound 12528 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12528 162).energyBound 12528 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12528 162) (d.f1 12528 162) d.f2 ≤
      32 * (((59270351 / 12500000000000000) : ℝ) + (395471873 / 250000000000000000) + (380207247 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12528 162) (d.w1 12528 162)
      (d.w2 12528 162) ≤
      32 * (((381950021 / 20000000000000000000) : ℝ) + (1358750737 / 100000000000000000000) + (49645371 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12528 162) (d.f1 12528 162) d.f2 ≤
      ((59270351 / 12500000000000000) : ℝ) ^ 2 + 2 * ((59270351 / 12500000000000000)) * ((395471873 / 250000000000000000)) * (126 / 100) +
      2 * (((395471873 / 250000000000000000)) ^ 2 + 2 * ((59270351 / 12500000000000000)) * ((380207247 / 1000000000000000000))) +
      6 * ((395471873 / 250000000000000000)) * ((380207247 / 1000000000000000000)) * (126 / 100) + 8 * ((380207247 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12528 162) (d.f1 12528 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12528 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12528 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12528 162) (d.f1 12528 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12528 162) (d.w1 12528 162) (d.w2 12528 162)
  have hwexpr0 : 0 ≤ d.w0 12528 162 + d.w1 12528 162 * √(π / 2) +
      2 * d.w2 12528 162 + energyR16 12528 *
      radiusPolynomialRoot16 (d.w0 12528 162) (d.w1 12528 162) (d.w2 12528 162) := by
    positivity
  constructor
  · change (12528 : ℝ) ^ 8 * (mA 12528 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12528 162) (d.f1 12528 162) d.f2 + locationR16 12528 *
        radiusPolynomialRoot16 (d.f0 12528 162) (d.f1 12528 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12528 : ℝ) ^ 8 * (mA 12528 : ℝ) ^ 8 *
        ((((59270351 / 12500000000000000) : ℝ) ^ 2 + 2 * ((59270351 / 12500000000000000)) * ((395471873 / 250000000000000000)) * (126 / 100) +
          2 * (((395471873 / 250000000000000000)) ^ 2 + 2 * ((59270351 / 12500000000000000)) * ((380207247 / 1000000000000000000))) +
          6 * ((395471873 / 250000000000000000)) * ((380207247 / 1000000000000000000)) * (126 / 100) + 8 * ((380207247 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12528) *
          (32 * (((59270351 / 12500000000000000) : ℝ) + (395471873 / 250000000000000000) + (380207247 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12528 : ℝ) ^ 16 *
      (d.w0 12528 162 + d.w1 12528 162 * √(π / 2) + 2 * d.w2 12528 162 +
        energyR16 12528 * radiusPolynomialRoot16 (d.w0 12528 162) (d.w1 12528 162)
          (d.w2 12528 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12528 : ℝ) ^ 16 *
        (((381950021 / 20000000000000000000) : ℝ) + ((1358750737 / 100000000000000000000)) * (126 / 100) + 2 * ((49645371 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12528) *
          (32 * (((381950021 / 20000000000000000000) : ℝ) + (1358750737 / 100000000000000000000) + (49645371 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12528

/-! A coarse bound on the actual paper statistics constant at dimension 12529. -/
namespace BstLean.Part266.Row12529
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12527 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12527 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12527 128 ≤ (12781 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12781 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12529) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12529 : ℕ))
    (by norm_num : (12529 : ℕ) ≤ 16384)
  have ht : paperTail256 12529 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12529 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12529 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12529 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12529 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12529 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12527 128 * √(2 / (12529 : ℝ)) *
      (√(12529 : ℝ) + paperT0 12529 + paperTail256 12529) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12529 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12529 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12529 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12527 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12527 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12529 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12529

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12529
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12529 (61 / 100) 162 (17 / (100 * 12529)) (26 / (10 * 12529)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12529 (61 / 100) 162 (17 / (100 * 12529)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (49632931 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (792288797 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5707032113 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12529 / 12529 * (61 / 100)) ^ 4 * inverseRadius8 (12529 - 1) /
            envelopeGap 12529 (61 / 100) 162 (17 / (100 * 12529)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12529

namespace BstLean.Part266.Row12529
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12529 162 ≤ (1185170477 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12529 162 ≤ (790785919 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (19006569 / 50000000000000000)
  w0 : (tableEnvelope C).w0 12529 162 ≤ (190929283 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 12529 162 ≤ (1358425397 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12529 162 ≤ (496334839 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (49632931 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (49632931 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (792288797 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5707032113 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3683547 / 1000000000) : ℝ) ≤ √(17 / (100 * 12529) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12529) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1113922473 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39806753121 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12529) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12529) ≤ (22575043 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12529) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12529 * (162 : ℝ) ^ 2 + 26 / (10 * 12529) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12529) : ℝ)) (tA 12529 * 162 ^ 2 + 26 / (10 * 12529)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3683547 / 1000000000))) * ((49632931 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3683547 / 1000000000)) ^ 3) * ((792288797 / 500000000000000000000000))) + ((5707032113 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3683547 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12529) : ℝ)) d.D d.V d.P (√(tA 12529) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3683547 / 1000000000)) ^ 2 * (((1113922473 / 500000000000000)) * ((39806753121 / 1000000000000000000)))) + ((5707032113 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12529) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3683547 / 1000000000)) * ((49632931 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12529) : ℝ)) (tA 12529 * 162 ^ 2 + 26 / (10 * 12529)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((49632931 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3683547 / 1000000000)) ^ 2) * ((792288797 / 500000000000000000000000)) + ((5707032113 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12529) : ℝ)) (√(26 / (10 * 12529) : ℝ)) d.D d.V d.P (√(tA 12529) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3683547 / 1000000000)) * (((1113922473 / 500000000000000)) * ((39806753121 / 1000000000000000000))) + ((5707032113 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12529) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((49632931 / 10000000000000000000) : ℝ) + ((5707032113 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12529

namespace BstLean.Part266.Row12529
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12529 162 ∧
    0 ≤ (tableEnvelope C).f1 12529 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12529 162 ∧
    0 ≤ (tableEnvelope C).w1 12529 162 ∧ 0 ≤ (tableEnvelope C).w2 12529 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12529 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12529 162 ∧ 0 ≤ d.f1 12529 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12529 162 ∧ 0 ≤ d.w1 12529 162 ∧ 0 ≤ d.w2 12529 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12529 ≤ 2 * (228 / 100 : ℝ) / 12529 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12529 ≤ 2 * (370 / 100 : ℝ) / 12529 := by
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
    (completeRAData (tableEnvelope C) 12529 162).locationBound 12529 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12529 162).energyBound 12529 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12529 162) (d.f1 12529 162) d.f2 ≤
      32 * (((1185170477 / 250000000000000000) : ℝ) + (790785919 / 500000000000000000) + (19006569 / 50000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12529 162) (d.w1 12529 162)
      (d.w2 12529 162) ≤
      32 * (((190929283 / 10000000000000000000) : ℝ) + (1358425397 / 100000000000000000000) + (496334839 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12529 162) (d.f1 12529 162) d.f2 ≤
      ((1185170477 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1185170477 / 250000000000000000)) * ((790785919 / 500000000000000000)) * (126 / 100) +
      2 * (((790785919 / 500000000000000000)) ^ 2 + 2 * ((1185170477 / 250000000000000000)) * ((19006569 / 50000000000000000))) +
      6 * ((790785919 / 500000000000000000)) * ((19006569 / 50000000000000000)) * (126 / 100) + 8 * ((19006569 / 50000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12529 162) (d.f1 12529 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12529 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12529 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12529 162) (d.f1 12529 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12529 162) (d.w1 12529 162) (d.w2 12529 162)
  have hwexpr0 : 0 ≤ d.w0 12529 162 + d.w1 12529 162 * √(π / 2) +
      2 * d.w2 12529 162 + energyR16 12529 *
      radiusPolynomialRoot16 (d.w0 12529 162) (d.w1 12529 162) (d.w2 12529 162) := by
    positivity
  constructor
  · change (12529 : ℝ) ^ 8 * (mA 12529 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12529 162) (d.f1 12529 162) d.f2 + locationR16 12529 *
        radiusPolynomialRoot16 (d.f0 12529 162) (d.f1 12529 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12529 : ℝ) ^ 8 * (mA 12529 : ℝ) ^ 8 *
        ((((1185170477 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1185170477 / 250000000000000000)) * ((790785919 / 500000000000000000)) * (126 / 100) +
          2 * (((790785919 / 500000000000000000)) ^ 2 + 2 * ((1185170477 / 250000000000000000)) * ((19006569 / 50000000000000000))) +
          6 * ((790785919 / 500000000000000000)) * ((19006569 / 50000000000000000)) * (126 / 100) + 8 * ((19006569 / 50000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12529) *
          (32 * (((1185170477 / 250000000000000000) : ℝ) + (790785919 / 500000000000000000) + (19006569 / 50000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12529 : ℝ) ^ 16 *
      (d.w0 12529 162 + d.w1 12529 162 * √(π / 2) + 2 * d.w2 12529 162 +
        energyR16 12529 * radiusPolynomialRoot16 (d.w0 12529 162) (d.w1 12529 162)
          (d.w2 12529 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12529 : ℝ) ^ 16 *
        (((190929283 / 10000000000000000000) : ℝ) + ((1358425397 / 100000000000000000000)) * (126 / 100) + 2 * ((496334839 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12529) *
          (32 * (((190929283 / 10000000000000000000) : ℝ) + (1358425397 / 100000000000000000000) + (496334839 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12529

/-! A coarse bound on the actual paper statistics constant at dimension 12530. -/
namespace BstLean.Part266.Row12530
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12528 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12528 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12528 128 ≤ (12782 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12782 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12530) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12530 : ℕ))
    (by norm_num : (12530 : ℕ) ≤ 16384)
  have ht : paperTail256 12530 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12530 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12530 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12530 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12530 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12530 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12528 128 * √(2 / (12530 : ℝ)) *
      (√(12530 : ℝ) + paperT0 12530 + paperTail256 12530) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12530 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12530 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12530 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12528 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12528 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12530 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12530

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12530
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12530 (61 / 100) 162 (17 / (100 * 12530)) (26 / (10 * 12530)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12530 (61 / 100) 162 (17 / (100 * 12530)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (496210479 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (198008973 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (178229793 / 31250000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12530 / 12530 * (61 / 100)) ^ 4 * inverseRadius8 (12530 - 1) /
            envelopeGap 12530 (61 / 100) 162 (17 / (100 * 12530)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12530

namespace BstLean.Part266.Row12530
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12530 162 ≤ (1184934017 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12530 162 ≤ (316251257 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (23753471 / 62500000000000000)
  w0 : (tableEnvelope C).w0 12530 162 ≤ (381767143 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12530 162 ≤ (679050083 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12530 162 ≤ (124054001 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (496210479 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (496210479 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (198008973 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (178229793 / 31250000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((18417 / 5000000) : ℝ) ≤ √(17 / (100 * 12530) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12530) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (445515647 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7960079859 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12530) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12530) ≤ (112866207 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12530) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12530 * (162 : ℝ) ^ 2 + 26 / (10 * 12530) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12530) : ℝ)) (tA 12530 * 162 ^ 2 + 26 / (10 * 12530)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((18417 / 5000000))) * ((496210479 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((18417 / 5000000)) ^ 3) * ((198008973 / 125000000000000000000000))) + ((178229793 / 31250000000000000000000)) * (3 / 2 * (39895 / 100000) / ((18417 / 5000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12530) : ℝ)) d.D d.V d.P (√(tA 12530) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((18417 / 5000000)) ^ 2 * (((445515647 / 200000000000000)) * ((7960079859 / 200000000000000000)))) + ((178229793 / 31250000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12530) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((18417 / 5000000)) * ((496210479 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12530) : ℝ)) (tA 12530 * 162 ^ 2 + 26 / (10 * 12530)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((496210479 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((18417 / 5000000)) ^ 2) * ((198008973 / 125000000000000000000000)) + ((178229793 / 31250000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12530) : ℝ)) (√(26 / (10 * 12530) : ℝ)) d.D d.V d.P (√(tA 12530) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((18417 / 5000000)) * (((445515647 / 200000000000000)) * ((7960079859 / 200000000000000000))) + ((178229793 / 31250000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12530) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((496210479 / 100000000000000000000) : ℝ) + ((178229793 / 31250000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12530

namespace BstLean.Part266.Row12530
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12530 162 ∧
    0 ≤ (tableEnvelope C).f1 12530 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12530 162 ∧
    0 ≤ (tableEnvelope C).w1 12530 162 ∧ 0 ≤ (tableEnvelope C).w2 12530 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12530 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12530 162 ∧ 0 ≤ d.f1 12530 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12530 162 ∧ 0 ≤ d.w1 12530 162 ∧ 0 ≤ d.w2 12530 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12530 ≤ 2 * (228 / 100 : ℝ) / 12530 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12530 ≤ 2 * (370 / 100 : ℝ) / 12530 := by
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
    (completeRAData (tableEnvelope C) 12530 162).locationBound 12530 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12530 162).energyBound 12530 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12530 162) (d.f1 12530 162) d.f2 ≤
      32 * (((1184934017 / 250000000000000000) : ℝ) + (316251257 / 200000000000000000) + (23753471 / 62500000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12530 162) (d.w1 12530 162)
      (d.w2 12530 162) ≤
      32 * (((381767143 / 20000000000000000000) : ℝ) + (679050083 / 50000000000000000000) + (124054001 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12530 162) (d.f1 12530 162) d.f2 ≤
      ((1184934017 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1184934017 / 250000000000000000)) * ((316251257 / 200000000000000000)) * (126 / 100) +
      2 * (((316251257 / 200000000000000000)) ^ 2 + 2 * ((1184934017 / 250000000000000000)) * ((23753471 / 62500000000000000))) +
      6 * ((316251257 / 200000000000000000)) * ((23753471 / 62500000000000000)) * (126 / 100) + 8 * ((23753471 / 62500000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12530 162) (d.f1 12530 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12530 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12530 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12530 162) (d.f1 12530 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12530 162) (d.w1 12530 162) (d.w2 12530 162)
  have hwexpr0 : 0 ≤ d.w0 12530 162 + d.w1 12530 162 * √(π / 2) +
      2 * d.w2 12530 162 + energyR16 12530 *
      radiusPolynomialRoot16 (d.w0 12530 162) (d.w1 12530 162) (d.w2 12530 162) := by
    positivity
  constructor
  · change (12530 : ℝ) ^ 8 * (mA 12530 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12530 162) (d.f1 12530 162) d.f2 + locationR16 12530 *
        radiusPolynomialRoot16 (d.f0 12530 162) (d.f1 12530 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12530 : ℝ) ^ 8 * (mA 12530 : ℝ) ^ 8 *
        ((((1184934017 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1184934017 / 250000000000000000)) * ((316251257 / 200000000000000000)) * (126 / 100) +
          2 * (((316251257 / 200000000000000000)) ^ 2 + 2 * ((1184934017 / 250000000000000000)) * ((23753471 / 62500000000000000))) +
          6 * ((316251257 / 200000000000000000)) * ((23753471 / 62500000000000000)) * (126 / 100) + 8 * ((23753471 / 62500000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12530) *
          (32 * (((1184934017 / 250000000000000000) : ℝ) + (316251257 / 200000000000000000) + (23753471 / 62500000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12530 : ℝ) ^ 16 *
      (d.w0 12530 162 + d.w1 12530 162 * √(π / 2) + 2 * d.w2 12530 162 +
        energyR16 12530 * radiusPolynomialRoot16 (d.w0 12530 162) (d.w1 12530 162)
          (d.w2 12530 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12530 : ℝ) ^ 16 *
        (((381767143 / 20000000000000000000) : ℝ) + ((679050083 / 50000000000000000000)) * (126 / 100) + 2 * ((124054001 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12530) *
          (32 * (((381767143 / 20000000000000000000) : ℝ) + (679050083 / 50000000000000000000) + (124054001 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12530

/-! A coarse bound on the actual paper statistics constant at dimension 12531. -/
namespace BstLean.Part266.Row12531
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12529 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12529 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12529 128 ≤ (12783 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12783 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12531) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12531 : ℕ))
    (by norm_num : (12531 : ℕ) ≤ 16384)
  have ht : paperTail256 12531 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12531 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12531 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12531 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12531 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12531 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12529 128 * √(2 / (12531 : ℝ)) *
      (√(12531 : ℝ) + paperT0 12531 + paperTail256 12531) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12531 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12531 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12531 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12529 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12529 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12531 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12531

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12531
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12531 (61 / 100) 162 (17 / (100 * 12531)) (26 / (10 * 12531)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12531 (61 / 100) 162 (17 / (100 * 12531)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (248045843 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (63342647 / 40000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1424919327 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12531 / 12531 * (61 / 100)) ^ 4 * inverseRadius8 (12531 - 1) /
            envelopeGap 12531 (61 / 100) 162 (17 / (100 * 12531)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12531

namespace BstLean.Part266.Row12531
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12531 162 ≤ (1184697639 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12531 162 ≤ (395235209 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (75995943 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12531 162 ≤ (954189379 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12531 162 ≤ (271555009 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12531 162 ≤ (62012151 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (248045843 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (248045843 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (63342647 / 40000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1424919327 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3683253 / 1000000000) : ℝ) ≤ √(17 / (100 * 12531) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12531) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2227311577 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1989702349 / 50000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12531) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12531) ≤ (282143 / 2500000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12531) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12531 * (162 : ℝ) ^ 2 + 26 / (10 * 12531) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12531) : ℝ)) (tA 12531 * 162 ^ 2 + 26 / (10 * 12531)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3683253 / 1000000000))) * ((248045843 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3683253 / 1000000000)) ^ 3) * ((63342647 / 40000000000000000000000))) + ((1424919327 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3683253 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12531) : ℝ)) d.D d.V d.P (√(tA 12531) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3683253 / 1000000000)) ^ 2 * (((2227311577 / 1000000000000000)) * ((1989702349 / 50000000000000000)))) + ((1424919327 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12531) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3683253 / 1000000000)) * ((248045843 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12531) : ℝ)) (tA 12531 * 162 ^ 2 + 26 / (10 * 12531)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((248045843 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3683253 / 1000000000)) ^ 2) * ((63342647 / 40000000000000000000000)) + ((1424919327 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12531) : ℝ)) (√(26 / (10 * 12531) : ℝ)) d.D d.V d.P (√(tA 12531) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3683253 / 1000000000)) * (((2227311577 / 1000000000000000)) * ((1989702349 / 50000000000000000))) + ((1424919327 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12531) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((248045843 / 50000000000000000000) : ℝ) + ((1424919327 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12531

namespace BstLean.Part266.Row12531
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12531 162 ∧
    0 ≤ (tableEnvelope C).f1 12531 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12531 162 ∧
    0 ≤ (tableEnvelope C).w1 12531 162 ∧ 0 ≤ (tableEnvelope C).w2 12531 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12531 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12531 162 ∧ 0 ≤ d.f1 12531 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12531 162 ∧ 0 ≤ d.w1 12531 162 ∧ 0 ≤ d.w2 12531 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12531 ≤ 2 * (228 / 100 : ℝ) / 12531 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12531 ≤ 2 * (370 / 100 : ℝ) / 12531 := by
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
    (completeRAData (tableEnvelope C) 12531 162).locationBound 12531 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12531 162).energyBound 12531 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12531 162) (d.f1 12531 162) d.f2 ≤
      32 * (((1184697639 / 250000000000000000) : ℝ) + (395235209 / 250000000000000000) + (75995943 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12531 162) (d.w1 12531 162)
      (d.w2 12531 162) ≤
      32 * (((954189379 / 50000000000000000000) : ℝ) + (271555009 / 20000000000000000000) + (62012151 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12531 162) (d.f1 12531 162) d.f2 ≤
      ((1184697639 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1184697639 / 250000000000000000)) * ((395235209 / 250000000000000000)) * (126 / 100) +
      2 * (((395235209 / 250000000000000000)) ^ 2 + 2 * ((1184697639 / 250000000000000000)) * ((75995943 / 200000000000000000))) +
      6 * ((395235209 / 250000000000000000)) * ((75995943 / 200000000000000000)) * (126 / 100) + 8 * ((75995943 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12531 162) (d.f1 12531 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12531 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12531 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12531 162) (d.f1 12531 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12531 162) (d.w1 12531 162) (d.w2 12531 162)
  have hwexpr0 : 0 ≤ d.w0 12531 162 + d.w1 12531 162 * √(π / 2) +
      2 * d.w2 12531 162 + energyR16 12531 *
      radiusPolynomialRoot16 (d.w0 12531 162) (d.w1 12531 162) (d.w2 12531 162) := by
    positivity
  constructor
  · change (12531 : ℝ) ^ 8 * (mA 12531 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12531 162) (d.f1 12531 162) d.f2 + locationR16 12531 *
        radiusPolynomialRoot16 (d.f0 12531 162) (d.f1 12531 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12531 : ℝ) ^ 8 * (mA 12531 : ℝ) ^ 8 *
        ((((1184697639 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1184697639 / 250000000000000000)) * ((395235209 / 250000000000000000)) * (126 / 100) +
          2 * (((395235209 / 250000000000000000)) ^ 2 + 2 * ((1184697639 / 250000000000000000)) * ((75995943 / 200000000000000000))) +
          6 * ((395235209 / 250000000000000000)) * ((75995943 / 200000000000000000)) * (126 / 100) + 8 * ((75995943 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12531) *
          (32 * (((1184697639 / 250000000000000000) : ℝ) + (395235209 / 250000000000000000) + (75995943 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12531 : ℝ) ^ 16 *
      (d.w0 12531 162 + d.w1 12531 162 * √(π / 2) + 2 * d.w2 12531 162 +
        energyR16 12531 * radiusPolynomialRoot16 (d.w0 12531 162) (d.w1 12531 162)
          (d.w2 12531 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12531 : ℝ) ^ 16 *
        (((954189379 / 50000000000000000000) : ℝ) + ((271555009 / 20000000000000000000)) * (126 / 100) + 2 * ((62012151 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12531) *
          (32 * (((954189379 / 50000000000000000000) : ℝ) + (271555009 / 20000000000000000000) + (62012151 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12531

/-! A coarse bound on the actual paper statistics constant at dimension 12532. -/
namespace BstLean.Part266.Row12532
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12530 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12530 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12530 128 ≤ (12784 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12784 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12532) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12532 : ℕ))
    (by norm_num : (12532 : ℕ) ≤ 16384)
  have ht : paperTail256 12532 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12532 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12532 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12532 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12532 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12532 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12530 128 * √(2 / (12532 : ℝ)) *
      (√(12532 : ℝ) + paperT0 12532 + paperTail256 12532) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12532 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12532 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12532 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12530 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12530 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12532 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12532

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12532
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12532 (61 / 100) 162 (17 / (100 * 12532)) (26 / (10 * 12532)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12532 (61 / 100) 162 (17 / (100 * 12532)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (495972931 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (49470649 / 31250000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5696003909 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12532 / 12532 * (61 / 100)) ^ 4 * inverseRadius8 (12532 - 1) /
            envelopeGap 12532 (61 / 100) 162 (17 / (100 * 12532)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12532

namespace BstLean.Part266.Row12532
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12532 162 ≤ (4737845373 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12532 162 ≤ (1580625491 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (189951959 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12532 162 ≤ (1907921961 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12532 162 ≤ (339362509 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12532 162 ≤ (495978449 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (495972931 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (495972931 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (49470649 / 31250000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5696003909 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1841553 / 500000000) : ℝ) ≤ √(17 / (100 * 12532) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12532) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2227044973 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39787696189 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12532) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12532) ≤ (56424097 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12532) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12532 * (162 : ℝ) ^ 2 + 26 / (10 * 12532) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12532) : ℝ)) (tA 12532 * 162 ^ 2 + 26 / (10 * 12532)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1841553 / 500000000))) * ((495972931 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1841553 / 500000000)) ^ 3) * ((49470649 / 31250000000000000000000))) + ((5696003909 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1841553 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12532) : ℝ)) d.D d.V d.P (√(tA 12532) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1841553 / 500000000)) ^ 2 * (((2227044973 / 1000000000000000)) * ((39787696189 / 1000000000000000000)))) + ((5696003909 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12532) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1841553 / 500000000)) * ((495972931 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12532) : ℝ)) (tA 12532 * 162 ^ 2 + 26 / (10 * 12532)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((495972931 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1841553 / 500000000)) ^ 2) * ((49470649 / 31250000000000000000000)) + ((5696003909 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12532) : ℝ)) (√(26 / (10 * 12532) : ℝ)) d.D d.V d.P (√(tA 12532) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1841553 / 500000000)) * (((2227044973 / 1000000000000000)) * ((39787696189 / 1000000000000000000))) + ((5696003909 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12532) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((495972931 / 100000000000000000000) : ℝ) + ((5696003909 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12532

namespace BstLean.Part266.Row12532
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12532 162 ∧
    0 ≤ (tableEnvelope C).f1 12532 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12532 162 ∧
    0 ≤ (tableEnvelope C).w1 12532 162 ∧ 0 ≤ (tableEnvelope C).w2 12532 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12532 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12532 162 ∧ 0 ≤ d.f1 12532 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12532 162 ∧ 0 ≤ d.w1 12532 162 ∧ 0 ≤ d.w2 12532 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12532 ≤ 2 * (228 / 100 : ℝ) / 12532 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12532 ≤ 2 * (370 / 100 : ℝ) / 12532 := by
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
    (completeRAData (tableEnvelope C) 12532 162).locationBound 12532 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12532 162).energyBound 12532 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12532 162) (d.f1 12532 162) d.f2 ≤
      32 * (((4737845373 / 1000000000000000000) : ℝ) + (1580625491 / 1000000000000000000) + (189951959 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12532 162) (d.w1 12532 162)
      (d.w2 12532 162) ≤
      32 * (((1907921961 / 100000000000000000000) : ℝ) + (339362509 / 25000000000000000000) + (495978449 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12532 162) (d.f1 12532 162) d.f2 ≤
      ((4737845373 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4737845373 / 1000000000000000000)) * ((1580625491 / 1000000000000000000)) * (126 / 100) +
      2 * (((1580625491 / 1000000000000000000)) ^ 2 + 2 * ((4737845373 / 1000000000000000000)) * ((189951959 / 500000000000000000))) +
      6 * ((1580625491 / 1000000000000000000)) * ((189951959 / 500000000000000000)) * (126 / 100) + 8 * ((189951959 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12532 162) (d.f1 12532 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12532 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12532 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12532 162) (d.f1 12532 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12532 162) (d.w1 12532 162) (d.w2 12532 162)
  have hwexpr0 : 0 ≤ d.w0 12532 162 + d.w1 12532 162 * √(π / 2) +
      2 * d.w2 12532 162 + energyR16 12532 *
      radiusPolynomialRoot16 (d.w0 12532 162) (d.w1 12532 162) (d.w2 12532 162) := by
    positivity
  constructor
  · change (12532 : ℝ) ^ 8 * (mA 12532 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12532 162) (d.f1 12532 162) d.f2 + locationR16 12532 *
        radiusPolynomialRoot16 (d.f0 12532 162) (d.f1 12532 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12532 : ℝ) ^ 8 * (mA 12532 : ℝ) ^ 8 *
        ((((4737845373 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4737845373 / 1000000000000000000)) * ((1580625491 / 1000000000000000000)) * (126 / 100) +
          2 * (((1580625491 / 1000000000000000000)) ^ 2 + 2 * ((4737845373 / 1000000000000000000)) * ((189951959 / 500000000000000000))) +
          6 * ((1580625491 / 1000000000000000000)) * ((189951959 / 500000000000000000)) * (126 / 100) + 8 * ((189951959 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12532) *
          (32 * (((4737845373 / 1000000000000000000) : ℝ) + (1580625491 / 1000000000000000000) + (189951959 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12532 : ℝ) ^ 16 *
      (d.w0 12532 162 + d.w1 12532 162 * √(π / 2) + 2 * d.w2 12532 162 +
        energyR16 12532 * radiusPolynomialRoot16 (d.w0 12532 162) (d.w1 12532 162)
          (d.w2 12532 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12532 : ℝ) ^ 16 *
        (((1907921961 / 100000000000000000000) : ℝ) + ((339362509 / 25000000000000000000)) * (126 / 100) + 2 * ((495978449 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12532) *
          (32 * (((1907921961 / 100000000000000000000) : ℝ) + (339362509 / 25000000000000000000) + (495978449 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12532

/-! A coarse bound on the actual paper statistics constant at dimension 12533. -/
namespace BstLean.Part266.Row12533
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12531 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12531 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12531 128 ≤ (12785 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12785 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12533) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12533 : ℕ))
    (by norm_num : (12533 : ℕ) ≤ 16384)
  have ht : paperTail256 12533 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12533 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12533 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12533 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12533 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12533 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12531 128 * √(2 / (12533 : ℝ)) *
      (√(12533 : ℝ) + paperT0 12533 + paperTail256 12533) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12533 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12533 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12533 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12531 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12531 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12533 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12533

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12533
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12533 (61 / 100) 162 (17 / (100 * 12533)) (26 / (10 * 12533)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12533 (61 / 100) 162 (17 / (100 * 12533)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (247927107 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1582555563 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (711541647 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12533 / 12533 * (61 / 100)) ^ 4 * inverseRadius8 (12533 - 1) /
            envelopeGap 12533 (61 / 100) 162 (17 / (100 * 12533)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12533

namespace BstLean.Part266.Row12533
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12533 162 ≤ (2368450261 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12533 162 ≤ (197538781 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (379828143 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12533 162 ≤ (476866331 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12533 162 ≤ (84820321 / 6250000000000000000)
  w2 : (tableEnvelope C).w2 12533 162 ≤ (495859729 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (247927107 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (247927107 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1582555563 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (711541647 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3682959 / 1000000000) : ℝ) ≤ √(17 / (100 * 12533) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12533) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1113389211 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39781346923 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12533) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12533) ≤ (11283919 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12533) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12533 * (162 : ℝ) ^ 2 + 26 / (10 * 12533) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12533) : ℝ)) (tA 12533 * 162 ^ 2 + 26 / (10 * 12533)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3682959 / 1000000000))) * ((247927107 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3682959 / 1000000000)) ^ 3) * ((1582555563 / 1000000000000000000000000))) + ((711541647 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3682959 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12533) : ℝ)) d.D d.V d.P (√(tA 12533) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3682959 / 1000000000)) ^ 2 * (((1113389211 / 500000000000000)) * ((39781346923 / 1000000000000000000)))) + ((711541647 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12533) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3682959 / 1000000000)) * ((247927107 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12533) : ℝ)) (tA 12533 * 162 ^ 2 + 26 / (10 * 12533)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((247927107 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3682959 / 1000000000)) ^ 2) * ((1582555563 / 1000000000000000000000000)) + ((711541647 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12533) : ℝ)) (√(26 / (10 * 12533) : ℝ)) d.D d.V d.P (√(tA 12533) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3682959 / 1000000000)) * (((1113389211 / 500000000000000)) * ((39781346923 / 1000000000000000000))) + ((711541647 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12533) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((247927107 / 50000000000000000000) : ℝ) + ((711541647 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12533

namespace BstLean.Part266.Row12533
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12533 162 ∧
    0 ≤ (tableEnvelope C).f1 12533 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12533 162 ∧
    0 ≤ (tableEnvelope C).w1 12533 162 ∧ 0 ≤ (tableEnvelope C).w2 12533 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12533 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12533 162 ∧ 0 ≤ d.f1 12533 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12533 162 ∧ 0 ≤ d.w1 12533 162 ∧ 0 ≤ d.w2 12533 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12533 ≤ 2 * (228 / 100 : ℝ) / 12533 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12533 ≤ 2 * (370 / 100 : ℝ) / 12533 := by
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
    (completeRAData (tableEnvelope C) 12533 162).locationBound 12533 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12533 162).energyBound 12533 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12533 162) (d.f1 12533 162) d.f2 ≤
      32 * (((2368450261 / 500000000000000000) : ℝ) + (197538781 / 125000000000000000) + (379828143 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12533 162) (d.w1 12533 162)
      (d.w2 12533 162) ≤
      32 * (((476866331 / 25000000000000000000) : ℝ) + (84820321 / 6250000000000000000) + (495859729 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12533 162) (d.f1 12533 162) d.f2 ≤
      ((2368450261 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2368450261 / 500000000000000000)) * ((197538781 / 125000000000000000)) * (126 / 100) +
      2 * (((197538781 / 125000000000000000)) ^ 2 + 2 * ((2368450261 / 500000000000000000)) * ((379828143 / 1000000000000000000))) +
      6 * ((197538781 / 125000000000000000)) * ((379828143 / 1000000000000000000)) * (126 / 100) + 8 * ((379828143 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12533 162) (d.f1 12533 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12533 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12533 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12533 162) (d.f1 12533 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12533 162) (d.w1 12533 162) (d.w2 12533 162)
  have hwexpr0 : 0 ≤ d.w0 12533 162 + d.w1 12533 162 * √(π / 2) +
      2 * d.w2 12533 162 + energyR16 12533 *
      radiusPolynomialRoot16 (d.w0 12533 162) (d.w1 12533 162) (d.w2 12533 162) := by
    positivity
  constructor
  · change (12533 : ℝ) ^ 8 * (mA 12533 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12533 162) (d.f1 12533 162) d.f2 + locationR16 12533 *
        radiusPolynomialRoot16 (d.f0 12533 162) (d.f1 12533 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12533 : ℝ) ^ 8 * (mA 12533 : ℝ) ^ 8 *
        ((((2368450261 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2368450261 / 500000000000000000)) * ((197538781 / 125000000000000000)) * (126 / 100) +
          2 * (((197538781 / 125000000000000000)) ^ 2 + 2 * ((2368450261 / 500000000000000000)) * ((379828143 / 1000000000000000000))) +
          6 * ((197538781 / 125000000000000000)) * ((379828143 / 1000000000000000000)) * (126 / 100) + 8 * ((379828143 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12533) *
          (32 * (((2368450261 / 500000000000000000) : ℝ) + (197538781 / 125000000000000000) + (379828143 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12533 : ℝ) ^ 16 *
      (d.w0 12533 162 + d.w1 12533 162 * √(π / 2) + 2 * d.w2 12533 162 +
        energyR16 12533 * radiusPolynomialRoot16 (d.w0 12533 162) (d.w1 12533 162)
          (d.w2 12533 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12533 : ℝ) ^ 16 *
        (((476866331 / 25000000000000000000) : ℝ) + ((84820321 / 6250000000000000000)) * (126 / 100) + 2 * ((495859729 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12533) *
          (32 * (((476866331 / 25000000000000000000) : ℝ) + (84820321 / 6250000000000000000) + (495859729 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12533

/-! A coarse bound on the actual paper statistics constant at dimension 12534. -/
namespace BstLean.Part266.Row12534
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12532 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12532 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12532 128 ≤ (12786 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12786 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12534) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12534 : ℕ))
    (by norm_num : (12534 : ℕ) ≤ 16384)
  have ht : paperTail256 12534 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12534 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12534 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12534 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12534 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12534 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12532 128 * √(2 / (12534 : ℝ)) *
      (√(12534 : ℝ) + paperT0 12534 + paperTail256 12534) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12534 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12534 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12534 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12532 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12532 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12534 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12534

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12534
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12534 (61 / 100) 162 (17 / (100 * 12534)) (26 / (10 * 12534)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12534 (61 / 100) 162 (17 / (100 * 12534)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (99147107 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1582050559 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5688665107 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12534 / 12534 * (61 / 100)) ^ 4 * inverseRadius8 (12534 - 1) /
            envelopeGap 12534 (61 / 100) 162 (17 / (100 * 12534)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12534

namespace BstLean.Part266.Row12534
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12534 162 ≤ (2367977999 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12534 162 ≤ (1579995109 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (379752391 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12534 162 ≤ (381401769 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12534 162 ≤ (1356800347 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12534 162 ≤ (247870523 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (99147107 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (99147107 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1582050559 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5688665107 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((920703 / 250000000) : ℝ) ≤ √(17 / (100 * 12534) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12534) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (89060477 / 40000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39774999171 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12534) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12534) ≤ (112830187 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12534) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12534 * (162 : ℝ) ^ 2 + 26 / (10 * 12534) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12534) : ℝ)) (tA 12534 * 162 ^ 2 + 26 / (10 * 12534)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((920703 / 250000000))) * ((99147107 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((920703 / 250000000)) ^ 3) * ((1582050559 / 1000000000000000000000000))) + ((5688665107 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((920703 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12534) : ℝ)) d.D d.V d.P (√(tA 12534) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((920703 / 250000000)) ^ 2 * (((89060477 / 40000000000000)) * ((39774999171 / 1000000000000000000)))) + ((5688665107 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12534) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((920703 / 250000000)) * ((99147107 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12534) : ℝ)) (tA 12534 * 162 ^ 2 + 26 / (10 * 12534)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((99147107 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((920703 / 250000000)) ^ 2) * ((1582050559 / 1000000000000000000000000)) + ((5688665107 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12534) : ℝ)) (√(26 / (10 * 12534) : ℝ)) d.D d.V d.P (√(tA 12534) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((920703 / 250000000)) * (((89060477 / 40000000000000)) * ((39774999171 / 1000000000000000000))) + ((5688665107 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12534) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((99147107 / 20000000000000000000) : ℝ) + ((5688665107 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12534

namespace BstLean.Part266.Row12534
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12534 162 ∧
    0 ≤ (tableEnvelope C).f1 12534 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12534 162 ∧
    0 ≤ (tableEnvelope C).w1 12534 162 ∧ 0 ≤ (tableEnvelope C).w2 12534 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12534 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12534 162 ∧ 0 ≤ d.f1 12534 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12534 162 ∧ 0 ≤ d.w1 12534 162 ∧ 0 ≤ d.w2 12534 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12534 ≤ 2 * (228 / 100 : ℝ) / 12534 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12534 ≤ 2 * (370 / 100 : ℝ) / 12534 := by
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
    (completeRAData (tableEnvelope C) 12534 162).locationBound 12534 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12534 162).energyBound 12534 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12534 162) (d.f1 12534 162) d.f2 ≤
      32 * (((2367977999 / 500000000000000000) : ℝ) + (1579995109 / 1000000000000000000) + (379752391 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12534 162) (d.w1 12534 162)
      (d.w2 12534 162) ≤
      32 * (((381401769 / 20000000000000000000) : ℝ) + (1356800347 / 100000000000000000000) + (247870523 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12534 162) (d.f1 12534 162) d.f2 ≤
      ((2367977999 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2367977999 / 500000000000000000)) * ((1579995109 / 1000000000000000000)) * (126 / 100) +
      2 * (((1579995109 / 1000000000000000000)) ^ 2 + 2 * ((2367977999 / 500000000000000000)) * ((379752391 / 1000000000000000000))) +
      6 * ((1579995109 / 1000000000000000000)) * ((379752391 / 1000000000000000000)) * (126 / 100) + 8 * ((379752391 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12534 162) (d.f1 12534 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12534 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12534 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12534 162) (d.f1 12534 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12534 162) (d.w1 12534 162) (d.w2 12534 162)
  have hwexpr0 : 0 ≤ d.w0 12534 162 + d.w1 12534 162 * √(π / 2) +
      2 * d.w2 12534 162 + energyR16 12534 *
      radiusPolynomialRoot16 (d.w0 12534 162) (d.w1 12534 162) (d.w2 12534 162) := by
    positivity
  constructor
  · change (12534 : ℝ) ^ 8 * (mA 12534 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12534 162) (d.f1 12534 162) d.f2 + locationR16 12534 *
        radiusPolynomialRoot16 (d.f0 12534 162) (d.f1 12534 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12534 : ℝ) ^ 8 * (mA 12534 : ℝ) ^ 8 *
        ((((2367977999 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2367977999 / 500000000000000000)) * ((1579995109 / 1000000000000000000)) * (126 / 100) +
          2 * (((1579995109 / 1000000000000000000)) ^ 2 + 2 * ((2367977999 / 500000000000000000)) * ((379752391 / 1000000000000000000))) +
          6 * ((1579995109 / 1000000000000000000)) * ((379752391 / 1000000000000000000)) * (126 / 100) + 8 * ((379752391 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12534) *
          (32 * (((2367977999 / 500000000000000000) : ℝ) + (1579995109 / 1000000000000000000) + (379752391 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12534 : ℝ) ^ 16 *
      (d.w0 12534 162 + d.w1 12534 162 * √(π / 2) + 2 * d.w2 12534 162 +
        energyR16 12534 * radiusPolynomialRoot16 (d.w0 12534 162) (d.w1 12534 162)
          (d.w2 12534 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12534 : ℝ) ^ 16 *
        (((381401769 / 20000000000000000000) : ℝ) + ((1356800347 / 100000000000000000000)) * (126 / 100) + 2 * ((247870523 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12534) *
          (32 * (((381401769 / 20000000000000000000) : ℝ) + (1356800347 / 100000000000000000000) + (247870523 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12534

/-! A coarse bound on the actual paper statistics constant at dimension 12535. -/
namespace BstLean.Part266.Row12535
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12533 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12533 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12533 128 ≤ (12787 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12787 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12535) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12535 : ℕ))
    (by norm_num : (12535 : ℕ) ≤ 16384)
  have ht : paperTail256 12535 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12535 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12535 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12535 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12535 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12535 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12533 128 * √(2 / (12535 : ℝ)) *
      (√(12535 : ℝ) + paperT0 12535 + paperTail256 12535) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12535 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12535 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12535 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12533 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12533 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12535 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12535

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12535
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12535 (61 / 100) 162 (17 / (100 * 12535)) (26 / (10 * 12535)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12535 (61 / 100) 162 (17 / (100 * 12535)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (247808447 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1581545757 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5684999699 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12535 / 12535 * (61 / 100)) ^ 4 * inverseRadius8 (12535 - 1) /
            envelopeGap 12535 (61 / 100) 162 (17 / (100 * 12535)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12535

namespace BstLean.Part266.Row12535
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12535 162 ≤ (1183752951 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12535 162 ≤ (789840037 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (189838331 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12535 162 ≤ (1906552527 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12535 162 ≤ (339118917 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12535 162 ≤ (495622401 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (247808447 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (247808447 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1581545757 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5684999699 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((736533 / 200000000) : ℝ) ≤ √(17 / (100 * 12535) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12535) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2226245481 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7953730589 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12535) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12535) ≤ (56410593 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12535) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12535 * (162 : ℝ) ^ 2 + 26 / (10 * 12535) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12535) : ℝ)) (tA 12535 * 162 ^ 2 + 26 / (10 * 12535)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((736533 / 200000000))) * ((247808447 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((736533 / 200000000)) ^ 3) * ((1581545757 / 1000000000000000000000000))) + ((5684999699 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((736533 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12535) : ℝ)) d.D d.V d.P (√(tA 12535) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((736533 / 200000000)) ^ 2 * (((2226245481 / 1000000000000000)) * ((7953730589 / 200000000000000000)))) + ((5684999699 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12535) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((736533 / 200000000)) * ((247808447 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12535) : ℝ)) (tA 12535 * 162 ^ 2 + 26 / (10 * 12535)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((247808447 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((736533 / 200000000)) ^ 2) * ((1581545757 / 1000000000000000000000000)) + ((5684999699 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12535) : ℝ)) (√(26 / (10 * 12535) : ℝ)) d.D d.V d.P (√(tA 12535) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((736533 / 200000000)) * (((2226245481 / 1000000000000000)) * ((7953730589 / 200000000000000000))) + ((5684999699 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12535) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((247808447 / 50000000000000000000) : ℝ) + ((5684999699 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12535

namespace BstLean.Part266.Row12535
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12535 162 ∧
    0 ≤ (tableEnvelope C).f1 12535 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12535 162 ∧
    0 ≤ (tableEnvelope C).w1 12535 162 ∧ 0 ≤ (tableEnvelope C).w2 12535 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12535 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12535 162 ∧ 0 ≤ d.f1 12535 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12535 162 ∧ 0 ≤ d.w1 12535 162 ∧ 0 ≤ d.w2 12535 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12535 ≤ 2 * (228 / 100 : ℝ) / 12535 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12535 ≤ 2 * (370 / 100 : ℝ) / 12535 := by
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
    (completeRAData (tableEnvelope C) 12535 162).locationBound 12535 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12535 162).energyBound 12535 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12535 162) (d.f1 12535 162) d.f2 ≤
      32 * (((1183752951 / 250000000000000000) : ℝ) + (789840037 / 500000000000000000) + (189838331 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12535 162) (d.w1 12535 162)
      (d.w2 12535 162) ≤
      32 * (((1906552527 / 100000000000000000000) : ℝ) + (339118917 / 25000000000000000000) + (495622401 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12535 162) (d.f1 12535 162) d.f2 ≤
      ((1183752951 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1183752951 / 250000000000000000)) * ((789840037 / 500000000000000000)) * (126 / 100) +
      2 * (((789840037 / 500000000000000000)) ^ 2 + 2 * ((1183752951 / 250000000000000000)) * ((189838331 / 500000000000000000))) +
      6 * ((789840037 / 500000000000000000)) * ((189838331 / 500000000000000000)) * (126 / 100) + 8 * ((189838331 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12535 162) (d.f1 12535 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12535 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12535 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12535 162) (d.f1 12535 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12535 162) (d.w1 12535 162) (d.w2 12535 162)
  have hwexpr0 : 0 ≤ d.w0 12535 162 + d.w1 12535 162 * √(π / 2) +
      2 * d.w2 12535 162 + energyR16 12535 *
      radiusPolynomialRoot16 (d.w0 12535 162) (d.w1 12535 162) (d.w2 12535 162) := by
    positivity
  constructor
  · change (12535 : ℝ) ^ 8 * (mA 12535 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12535 162) (d.f1 12535 162) d.f2 + locationR16 12535 *
        radiusPolynomialRoot16 (d.f0 12535 162) (d.f1 12535 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12535 : ℝ) ^ 8 * (mA 12535 : ℝ) ^ 8 *
        ((((1183752951 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1183752951 / 250000000000000000)) * ((789840037 / 500000000000000000)) * (126 / 100) +
          2 * (((789840037 / 500000000000000000)) ^ 2 + 2 * ((1183752951 / 250000000000000000)) * ((189838331 / 500000000000000000))) +
          6 * ((789840037 / 500000000000000000)) * ((189838331 / 500000000000000000)) * (126 / 100) + 8 * ((189838331 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12535) *
          (32 * (((1183752951 / 250000000000000000) : ℝ) + (789840037 / 500000000000000000) + (189838331 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12535 : ℝ) ^ 16 *
      (d.w0 12535 162 + d.w1 12535 162 * √(π / 2) + 2 * d.w2 12535 162 +
        energyR16 12535 * radiusPolynomialRoot16 (d.w0 12535 162) (d.w1 12535 162)
          (d.w2 12535 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12535 : ℝ) ^ 16 *
        (((1906552527 / 100000000000000000000) : ℝ) + ((339118917 / 25000000000000000000)) * (126 / 100) + 2 * ((495622401 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12535) *
          (32 * (((1906552527 / 100000000000000000000) : ℝ) + (339118917 / 25000000000000000000) + (495622401 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12535

/-! A coarse bound on the actual paper statistics constant at dimension 12536. -/
namespace BstLean.Part266.Row12536
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12534 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12534 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12534 128 ≤ (12788 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12788 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12536) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12536 : ℕ))
    (by norm_num : (12536 : ℕ) ≤ 16384)
  have ht : paperTail256 12536 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12536 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12536 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12536 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12536 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12536 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12534 128 * √(2 / (12536 : ℝ)) *
      (√(12536 : ℝ) + paperT0 12536 + paperTail256 12536) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12536 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12536 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12536 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12534 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12534 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12536 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12536

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12536
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12536 (61 / 100) 162 (17 / (100 * 12536)) (26 / (10 * 12536)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12536 (61 / 100) 162 (17 / (100 * 12536)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (495498291 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (395260289 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5681336951 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12536 / 12536 * (61 / 100)) ^ 4 * inverseRadius8 (12536 - 1) /
            envelopeGap 12536 (61 / 100) 162 (17 / (100 * 12536)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12536

namespace BstLean.Part266.Row12536
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12536 162 ≤ (4734067939 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12536 162 ≤ (789682571 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (379600957 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12536 162 ≤ (1906096367 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12536 162 ≤ (1356151099 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12536 162 ≤ (99100759 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (495498291 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (495498291 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (395260289 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5681336951 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1841259 / 500000000) : ℝ) ≤ √(17 / (100 * 12536) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12536) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2225979091 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39762308233 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12536) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12536) ≤ (56406093 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12536) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12536 * (162 : ℝ) ^ 2 + 26 / (10 * 12536) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12536) : ℝ)) (tA 12536 * 162 ^ 2 + 26 / (10 * 12536)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1841259 / 500000000))) * ((495498291 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1841259 / 500000000)) ^ 3) * ((395260289 / 250000000000000000000000))) + ((5681336951 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1841259 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12536) : ℝ)) d.D d.V d.P (√(tA 12536) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1841259 / 500000000)) ^ 2 * (((2225979091 / 1000000000000000)) * ((39762308233 / 1000000000000000000)))) + ((5681336951 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12536) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1841259 / 500000000)) * ((495498291 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12536) : ℝ)) (tA 12536 * 162 ^ 2 + 26 / (10 * 12536)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((495498291 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1841259 / 500000000)) ^ 2) * ((395260289 / 250000000000000000000000)) + ((5681336951 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12536) : ℝ)) (√(26 / (10 * 12536) : ℝ)) d.D d.V d.P (√(tA 12536) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1841259 / 500000000)) * (((2225979091 / 1000000000000000)) * ((39762308233 / 1000000000000000000))) + ((5681336951 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12536) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((495498291 / 100000000000000000000) : ℝ) + ((5681336951 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12536

namespace BstLean.Part266.Row12536
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12536 162 ∧
    0 ≤ (tableEnvelope C).f1 12536 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12536 162 ∧
    0 ≤ (tableEnvelope C).w1 12536 162 ∧ 0 ≤ (tableEnvelope C).w2 12536 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12536 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12536 162 ∧ 0 ≤ d.f1 12536 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12536 162 ∧ 0 ≤ d.w1 12536 162 ∧ 0 ≤ d.w2 12536 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12536 ≤ 2 * (228 / 100 : ℝ) / 12536 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12536 ≤ 2 * (370 / 100 : ℝ) / 12536 := by
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
    (completeRAData (tableEnvelope C) 12536 162).locationBound 12536 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12536 162).energyBound 12536 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12536 162) (d.f1 12536 162) d.f2 ≤
      32 * (((4734067939 / 1000000000000000000) : ℝ) + (789682571 / 500000000000000000) + (379600957 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12536 162) (d.w1 12536 162)
      (d.w2 12536 162) ≤
      32 * (((1906096367 / 100000000000000000000) : ℝ) + (1356151099 / 100000000000000000000) + (99100759 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12536 162) (d.f1 12536 162) d.f2 ≤
      ((4734067939 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4734067939 / 1000000000000000000)) * ((789682571 / 500000000000000000)) * (126 / 100) +
      2 * (((789682571 / 500000000000000000)) ^ 2 + 2 * ((4734067939 / 1000000000000000000)) * ((379600957 / 1000000000000000000))) +
      6 * ((789682571 / 500000000000000000)) * ((379600957 / 1000000000000000000)) * (126 / 100) + 8 * ((379600957 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12536 162) (d.f1 12536 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12536 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12536 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12536 162) (d.f1 12536 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12536 162) (d.w1 12536 162) (d.w2 12536 162)
  have hwexpr0 : 0 ≤ d.w0 12536 162 + d.w1 12536 162 * √(π / 2) +
      2 * d.w2 12536 162 + energyR16 12536 *
      radiusPolynomialRoot16 (d.w0 12536 162) (d.w1 12536 162) (d.w2 12536 162) := by
    positivity
  constructor
  · change (12536 : ℝ) ^ 8 * (mA 12536 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12536 162) (d.f1 12536 162) d.f2 + locationR16 12536 *
        radiusPolynomialRoot16 (d.f0 12536 162) (d.f1 12536 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12536 : ℝ) ^ 8 * (mA 12536 : ℝ) ^ 8 *
        ((((4734067939 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4734067939 / 1000000000000000000)) * ((789682571 / 500000000000000000)) * (126 / 100) +
          2 * (((789682571 / 500000000000000000)) ^ 2 + 2 * ((4734067939 / 1000000000000000000)) * ((379600957 / 1000000000000000000))) +
          6 * ((789682571 / 500000000000000000)) * ((379600957 / 1000000000000000000)) * (126 / 100) + 8 * ((379600957 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12536) *
          (32 * (((4734067939 / 1000000000000000000) : ℝ) + (789682571 / 500000000000000000) + (379600957 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12536 : ℝ) ^ 16 *
      (d.w0 12536 162 + d.w1 12536 162 * √(π / 2) + 2 * d.w2 12536 162 +
        energyR16 12536 * radiusPolynomialRoot16 (d.w0 12536 162) (d.w1 12536 162)
          (d.w2 12536 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12536 : ℝ) ^ 16 *
        (((1906096367 / 100000000000000000000) : ℝ) + ((1356151099 / 100000000000000000000)) * (126 / 100) + 2 * ((99100759 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12536) *
          (32 * (((1906096367 / 100000000000000000000) : ℝ) + (1356151099 / 100000000000000000000) + (99100759 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12536

/-! A coarse bound on the actual paper statistics constant at dimension 12537. -/
namespace BstLean.Part266.Row12537
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12535 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12535 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12535 128 ≤ (12789 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12789 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12537) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12537 : ℕ))
    (by norm_num : (12537 : ℕ) ≤ 16384)
  have ht : paperTail256 12537 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12537 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12537 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12537 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12537 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12537 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12535 128 * √(2 / (12537 : ℝ)) *
      (√(12537 : ℝ) + paperT0 12537 + paperTail256 12537) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12537 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12537 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12537 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12535 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12535 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12537 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12537

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12537
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12537 (61 / 100) 162 (17 / (100 * 12537)) (26 / (10 * 12537)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12537 (61 / 100) 162 (17 / (100 * 12537)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (19815189 / 4000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (395134189 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (283883843 / 50000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12537 / 12537 * (61 / 100)) ^ 4 * inverseRadius8 (12537 - 1) /
            envelopeGap 12537 (61 / 100) 162 (17 / (100 * 12537)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12537

namespace BstLean.Part266.Row12537
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12537 162 ≤ (4733124401 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12537 162 ≤ (1579050311 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (379525273 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12537 162 ≤ (381128073 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12537 162 ≤ (1355826639 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12537 162 ≤ (19815409 / 4000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (19815189 / 4000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (19815189 / 4000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (395134189 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (283883843 / 50000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3682371 / 1000000000) : ℝ) ≤ √(17 / (100 * 12537) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12537) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (139107047 / 62500000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39755965037 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12537) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12537) ≤ (28200797 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12537) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12537 * (162 : ℝ) ^ 2 + 26 / (10 * 12537) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12537) : ℝ)) (tA 12537 * 162 ^ 2 + 26 / (10 * 12537)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3682371 / 1000000000))) * ((19815189 / 4000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3682371 / 1000000000)) ^ 3) * ((395134189 / 250000000000000000000000))) + ((283883843 / 50000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3682371 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12537) : ℝ)) d.D d.V d.P (√(tA 12537) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3682371 / 1000000000)) ^ 2 * (((139107047 / 62500000000000)) * ((39755965037 / 1000000000000000000)))) + ((283883843 / 50000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12537) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3682371 / 1000000000)) * ((19815189 / 4000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12537) : ℝ)) (tA 12537 * 162 ^ 2 + 26 / (10 * 12537)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((19815189 / 4000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3682371 / 1000000000)) ^ 2) * ((395134189 / 250000000000000000000000)) + ((283883843 / 50000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12537) : ℝ)) (√(26 / (10 * 12537) : ℝ)) d.D d.V d.P (√(tA 12537) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3682371 / 1000000000)) * (((139107047 / 62500000000000)) * ((39755965037 / 1000000000000000000))) + ((283883843 / 50000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12537) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((19815189 / 4000000000000000000) : ℝ) + ((283883843 / 50000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12537

namespace BstLean.Part266.Row12537
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12537 162 ∧
    0 ≤ (tableEnvelope C).f1 12537 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12537 162 ∧
    0 ≤ (tableEnvelope C).w1 12537 162 ∧ 0 ≤ (tableEnvelope C).w2 12537 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12537 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12537 162 ∧ 0 ≤ d.f1 12537 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12537 162 ∧ 0 ≤ d.w1 12537 162 ∧ 0 ≤ d.w2 12537 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12537 ≤ 2 * (228 / 100 : ℝ) / 12537 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12537 ≤ 2 * (370 / 100 : ℝ) / 12537 := by
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
    (completeRAData (tableEnvelope C) 12537 162).locationBound 12537 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12537 162).energyBound 12537 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12537 162) (d.f1 12537 162) d.f2 ≤
      32 * (((4733124401 / 1000000000000000000) : ℝ) + (1579050311 / 1000000000000000000) + (379525273 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12537 162) (d.w1 12537 162)
      (d.w2 12537 162) ≤
      32 * (((381128073 / 20000000000000000000) : ℝ) + (1355826639 / 100000000000000000000) + (19815409 / 4000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12537 162) (d.f1 12537 162) d.f2 ≤
      ((4733124401 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4733124401 / 1000000000000000000)) * ((1579050311 / 1000000000000000000)) * (126 / 100) +
      2 * (((1579050311 / 1000000000000000000)) ^ 2 + 2 * ((4733124401 / 1000000000000000000)) * ((379525273 / 1000000000000000000))) +
      6 * ((1579050311 / 1000000000000000000)) * ((379525273 / 1000000000000000000)) * (126 / 100) + 8 * ((379525273 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12537 162) (d.f1 12537 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12537 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12537 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12537 162) (d.f1 12537 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12537 162) (d.w1 12537 162) (d.w2 12537 162)
  have hwexpr0 : 0 ≤ d.w0 12537 162 + d.w1 12537 162 * √(π / 2) +
      2 * d.w2 12537 162 + energyR16 12537 *
      radiusPolynomialRoot16 (d.w0 12537 162) (d.w1 12537 162) (d.w2 12537 162) := by
    positivity
  constructor
  · change (12537 : ℝ) ^ 8 * (mA 12537 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12537 162) (d.f1 12537 162) d.f2 + locationR16 12537 *
        radiusPolynomialRoot16 (d.f0 12537 162) (d.f1 12537 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12537 : ℝ) ^ 8 * (mA 12537 : ℝ) ^ 8 *
        ((((4733124401 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4733124401 / 1000000000000000000)) * ((1579050311 / 1000000000000000000)) * (126 / 100) +
          2 * (((1579050311 / 1000000000000000000)) ^ 2 + 2 * ((4733124401 / 1000000000000000000)) * ((379525273 / 1000000000000000000))) +
          6 * ((1579050311 / 1000000000000000000)) * ((379525273 / 1000000000000000000)) * (126 / 100) + 8 * ((379525273 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12537) *
          (32 * (((4733124401 / 1000000000000000000) : ℝ) + (1579050311 / 1000000000000000000) + (379525273 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12537 : ℝ) ^ 16 *
      (d.w0 12537 162 + d.w1 12537 162 * √(π / 2) + 2 * d.w2 12537 162 +
        energyR16 12537 * radiusPolynomialRoot16 (d.w0 12537 162) (d.w1 12537 162)
          (d.w2 12537 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12537 : ℝ) ^ 16 *
        (((381128073 / 20000000000000000000) : ℝ) + ((1355826639 / 100000000000000000000)) * (126 / 100) + 2 * ((19815409 / 4000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12537) *
          (32 * (((381128073 / 20000000000000000000) : ℝ) + (1355826639 / 100000000000000000000) + (19815409 / 4000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12537

/-! A coarse bound on the actual paper statistics constant at dimension 12538. -/
namespace BstLean.Part266.Row12538
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12536 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12536 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12536 128 ≤ (12790 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12790 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12538) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12538 : ℕ))
    (by norm_num : (12538 : ℕ) ≤ 16384)
  have ht : paperTail256 12538 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12538 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12538 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12538 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12538 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12538 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12536 128 * √(2 / (12538 : ℝ)) *
      (√(12538 : ℝ) + paperT0 12538 + paperTail256 12538) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12538 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12538 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12538 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12536 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12536 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12538 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12538

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12538
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12538 (61 / 100) 162 (17 / (100 * 12538)) (26 / (10 * 12538)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12538 (61 / 100) 162 (17 / (100 * 12538)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (247630599 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1580032557 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (226960777 / 40000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12538 / 12538 * (61 / 100)) ^ 4 * inverseRadius8 (12538 - 1) /
            envelopeGap 12538 (61 / 100) 162 (17 / (100 * 12538)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12538

namespace BstLean.Part266.Row12538
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12538 162 ≤ (2366088741 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12538 162 ≤ (1578734727 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (379449511 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12538 162 ≤ (952591879 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12538 162 ≤ (677750961 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12538 162 ≤ (99053339 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (247630599 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (247630599 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1580032557 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (226960777 / 40000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((147289 / 40000000) : ℝ) ≤ √(17 / (100 * 12538) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12538) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (556361617 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39749623357 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12538) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12538) ≤ (112794191 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12538) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12538 * (162 : ℝ) ^ 2 + 26 / (10 * 12538) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12538) : ℝ)) (tA 12538 * 162 ^ 2 + 26 / (10 * 12538)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((147289 / 40000000))) * ((247630599 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((147289 / 40000000)) ^ 3) * ((1580032557 / 1000000000000000000000000))) + ((226960777 / 40000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((147289 / 40000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12538) : ℝ)) d.D d.V d.P (√(tA 12538) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((147289 / 40000000)) ^ 2 * (((556361617 / 250000000000000)) * ((39749623357 / 1000000000000000000)))) + ((226960777 / 40000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12538) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((147289 / 40000000)) * ((247630599 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12538) : ℝ)) (tA 12538 * 162 ^ 2 + 26 / (10 * 12538)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((247630599 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((147289 / 40000000)) ^ 2) * ((1580032557 / 1000000000000000000000000)) + ((226960777 / 40000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12538) : ℝ)) (√(26 / (10 * 12538) : ℝ)) d.D d.V d.P (√(tA 12538) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((147289 / 40000000)) * (((556361617 / 250000000000000)) * ((39749623357 / 1000000000000000000))) + ((226960777 / 40000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12538) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((247630599 / 50000000000000000000) : ℝ) + ((226960777 / 40000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12538

namespace BstLean.Part266.Row12538
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12538 162 ∧
    0 ≤ (tableEnvelope C).f1 12538 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12538 162 ∧
    0 ≤ (tableEnvelope C).w1 12538 162 ∧ 0 ≤ (tableEnvelope C).w2 12538 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12538 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12538 162 ∧ 0 ≤ d.f1 12538 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12538 162 ∧ 0 ≤ d.w1 12538 162 ∧ 0 ≤ d.w2 12538 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12538 ≤ 2 * (228 / 100 : ℝ) / 12538 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12538 ≤ 2 * (370 / 100 : ℝ) / 12538 := by
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
    (completeRAData (tableEnvelope C) 12538 162).locationBound 12538 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12538 162).energyBound 12538 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12538 162) (d.f1 12538 162) d.f2 ≤
      32 * (((2366088741 / 500000000000000000) : ℝ) + (1578734727 / 1000000000000000000) + (379449511 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12538 162) (d.w1 12538 162)
      (d.w2 12538 162) ≤
      32 * (((952591879 / 50000000000000000000) : ℝ) + (677750961 / 50000000000000000000) + (99053339 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12538 162) (d.f1 12538 162) d.f2 ≤
      ((2366088741 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2366088741 / 500000000000000000)) * ((1578734727 / 1000000000000000000)) * (126 / 100) +
      2 * (((1578734727 / 1000000000000000000)) ^ 2 + 2 * ((2366088741 / 500000000000000000)) * ((379449511 / 1000000000000000000))) +
      6 * ((1578734727 / 1000000000000000000)) * ((379449511 / 1000000000000000000)) * (126 / 100) + 8 * ((379449511 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12538 162) (d.f1 12538 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12538 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12538 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12538 162) (d.f1 12538 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12538 162) (d.w1 12538 162) (d.w2 12538 162)
  have hwexpr0 : 0 ≤ d.w0 12538 162 + d.w1 12538 162 * √(π / 2) +
      2 * d.w2 12538 162 + energyR16 12538 *
      radiusPolynomialRoot16 (d.w0 12538 162) (d.w1 12538 162) (d.w2 12538 162) := by
    positivity
  constructor
  · change (12538 : ℝ) ^ 8 * (mA 12538 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12538 162) (d.f1 12538 162) d.f2 + locationR16 12538 *
        radiusPolynomialRoot16 (d.f0 12538 162) (d.f1 12538 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12538 : ℝ) ^ 8 * (mA 12538 : ℝ) ^ 8 *
        ((((2366088741 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2366088741 / 500000000000000000)) * ((1578734727 / 1000000000000000000)) * (126 / 100) +
          2 * (((1578734727 / 1000000000000000000)) ^ 2 + 2 * ((2366088741 / 500000000000000000)) * ((379449511 / 1000000000000000000))) +
          6 * ((1578734727 / 1000000000000000000)) * ((379449511 / 1000000000000000000)) * (126 / 100) + 8 * ((379449511 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12538) *
          (32 * (((2366088741 / 500000000000000000) : ℝ) + (1578734727 / 1000000000000000000) + (379449511 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12538 : ℝ) ^ 16 *
      (d.w0 12538 162 + d.w1 12538 162 * √(π / 2) + 2 * d.w2 12538 162 +
        energyR16 12538 * radiusPolynomialRoot16 (d.w0 12538 162) (d.w1 12538 162)
          (d.w2 12538 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12538 : ℝ) ^ 16 *
        (((952591879 / 50000000000000000000) : ℝ) + ((677750961 / 50000000000000000000)) * (126 / 100) + 2 * ((99053339 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12538) *
          (32 * (((952591879 / 50000000000000000000) : ℝ) + (677750961 / 50000000000000000000) + (99053339 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12538

/-! A coarse bound on the actual paper statistics constant at dimension 12539. -/
namespace BstLean.Part266.Row12539
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12537 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12537 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12537 128 ≤ (12791 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12791 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12539) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12539 : ℕ))
    (by norm_num : (12539 : ℕ) ≤ 16384)
  have ht : paperTail256 12539 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12539 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12539 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12539 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12539 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12539 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12537 128 * √(2 / (12539 : ℝ)) *
      (√(12539 : ℝ) + paperT0 12539 + paperTail256 12539) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12539 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12539 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12539 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12537 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12537 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12539 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12539

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12539
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12539 (61 / 100) 162 (17 / (100 * 12539)) (26 / (10 * 12539)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12539 (61 / 100) 162 (17 / (100 * 12539)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (123785677 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (19744107 / 12500000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5670364643 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12539 / 12539 * (61 / 100)) ^ 4 * inverseRadius8 (12539 - 1) /
            envelopeGap 12539 (61 / 100) 162 (17 / (100 * 12539)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12539

namespace BstLean.Part266.Row12539
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12539 162 ≤ (946246921 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12539 162 ≤ (1578420103 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (189686937 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12539 162 ≤ (76189123 / 4000000000000000000)
  w1 : (tableEnvelope C).w1 12539 162 ≤ (1355177683 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12539 162 ≤ (495148201 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (123785677 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (123785677 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (19744107 / 12500000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5670364643 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1841039 / 500000000) : ℝ) ≤ √(17 / (100 * 12539) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12539) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (556295059 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39743283207 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12539) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12539) ≤ (28196299 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12539) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12539 * (162 : ℝ) ^ 2 + 26 / (10 * 12539) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12539) : ℝ)) (tA 12539 * 162 ^ 2 + 26 / (10 * 12539)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1841039 / 500000000))) * ((123785677 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1841039 / 500000000)) ^ 3) * ((19744107 / 12500000000000000000000))) + ((5670364643 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1841039 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12539) : ℝ)) d.D d.V d.P (√(tA 12539) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1841039 / 500000000)) ^ 2 * (((556295059 / 250000000000000)) * ((39743283207 / 1000000000000000000)))) + ((5670364643 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12539) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1841039 / 500000000)) * ((123785677 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12539) : ℝ)) (tA 12539 * 162 ^ 2 + 26 / (10 * 12539)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((123785677 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1841039 / 500000000)) ^ 2) * ((19744107 / 12500000000000000000000)) + ((5670364643 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12539) : ℝ)) (√(26 / (10 * 12539) : ℝ)) d.D d.V d.P (√(tA 12539) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1841039 / 500000000)) * (((556295059 / 250000000000000)) * ((39743283207 / 1000000000000000000))) + ((5670364643 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12539) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((123785677 / 25000000000000000000) : ℝ) + ((5670364643 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12539

namespace BstLean.Part266.Row12539
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12539 162 ∧
    0 ≤ (tableEnvelope C).f1 12539 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12539 162 ∧
    0 ≤ (tableEnvelope C).w1 12539 162 ∧ 0 ≤ (tableEnvelope C).w2 12539 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12539 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12539 162 ∧ 0 ≤ d.f1 12539 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12539 162 ∧ 0 ≤ d.w1 12539 162 ∧ 0 ≤ d.w2 12539 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12539 ≤ 2 * (228 / 100 : ℝ) / 12539 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12539 ≤ 2 * (370 / 100 : ℝ) / 12539 := by
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
    (completeRAData (tableEnvelope C) 12539 162).locationBound 12539 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12539 162).energyBound 12539 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12539 162) (d.f1 12539 162) d.f2 ≤
      32 * (((946246921 / 200000000000000000) : ℝ) + (1578420103 / 1000000000000000000) + (189686937 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12539 162) (d.w1 12539 162)
      (d.w2 12539 162) ≤
      32 * (((76189123 / 4000000000000000000) : ℝ) + (1355177683 / 100000000000000000000) + (495148201 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12539 162) (d.f1 12539 162) d.f2 ≤
      ((946246921 / 200000000000000000) : ℝ) ^ 2 + 2 * ((946246921 / 200000000000000000)) * ((1578420103 / 1000000000000000000)) * (126 / 100) +
      2 * (((1578420103 / 1000000000000000000)) ^ 2 + 2 * ((946246921 / 200000000000000000)) * ((189686937 / 500000000000000000))) +
      6 * ((1578420103 / 1000000000000000000)) * ((189686937 / 500000000000000000)) * (126 / 100) + 8 * ((189686937 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12539 162) (d.f1 12539 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12539 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12539 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12539 162) (d.f1 12539 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12539 162) (d.w1 12539 162) (d.w2 12539 162)
  have hwexpr0 : 0 ≤ d.w0 12539 162 + d.w1 12539 162 * √(π / 2) +
      2 * d.w2 12539 162 + energyR16 12539 *
      radiusPolynomialRoot16 (d.w0 12539 162) (d.w1 12539 162) (d.w2 12539 162) := by
    positivity
  constructor
  · change (12539 : ℝ) ^ 8 * (mA 12539 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12539 162) (d.f1 12539 162) d.f2 + locationR16 12539 *
        radiusPolynomialRoot16 (d.f0 12539 162) (d.f1 12539 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12539 : ℝ) ^ 8 * (mA 12539 : ℝ) ^ 8 *
        ((((946246921 / 200000000000000000) : ℝ) ^ 2 + 2 * ((946246921 / 200000000000000000)) * ((1578420103 / 1000000000000000000)) * (126 / 100) +
          2 * (((1578420103 / 1000000000000000000)) ^ 2 + 2 * ((946246921 / 200000000000000000)) * ((189686937 / 500000000000000000))) +
          6 * ((1578420103 / 1000000000000000000)) * ((189686937 / 500000000000000000)) * (126 / 100) + 8 * ((189686937 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12539) *
          (32 * (((946246921 / 200000000000000000) : ℝ) + (1578420103 / 1000000000000000000) + (189686937 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12539 : ℝ) ^ 16 *
      (d.w0 12539 162 + d.w1 12539 162 * √(π / 2) + 2 * d.w2 12539 162 +
        energyR16 12539 * radiusPolynomialRoot16 (d.w0 12539 162) (d.w1 12539 162)
          (d.w2 12539 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12539 : ℝ) ^ 16 *
        (((76189123 / 4000000000000000000) : ℝ) + ((1355177683 / 100000000000000000000)) * (126 / 100) + 2 * ((495148201 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12539) *
          (32 * (((76189123 / 4000000000000000000) : ℝ) + (1355177683 / 100000000000000000000) + (495148201 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12539

/-! A coarse bound on the actual paper statistics constant at dimension 12540. -/
namespace BstLean.Part266.Row12540
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12538 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12538 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12538 128 ≤ (12792 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12792 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12540) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12540 : ℕ))
    (by norm_num : (12540 : ℕ) ≤ 16384)
  have ht : paperTail256 12540 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12540 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12540 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12540 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12540 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12540 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12538 128 * √(2 / (12540 : ℝ)) *
      (√(12540 : ℝ) + paperT0 12540 + paperTail256 12540) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12540 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12540 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12540 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12538 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12538 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12540 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12540

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12540
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12540 (61 / 100) 162 (17 / (100 * 12540)) (26 / (10 * 12540)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12540 (61 / 100) 162 (17 / (100 * 12540)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (3867377 / 781250000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1579024763 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5666712511 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12540 / 12540 * (61 / 100)) ^ 4 * inverseRadius8 (12540 - 1) /
            envelopeGap 12540 (61 / 100) 162 (17 / (100 * 12540)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12540

namespace BstLean.Part266.Row12540
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12540 162 ≤ (4730292053 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12540 162 ≤ (789052791 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (18964913 / 50000000000000000)
  w0 : (tableEnvelope C).w0 12540 162 ≤ (1904272551 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12540 162 ≤ (677426777 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12540 162 ≤ (247514873 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (3867377 / 781250000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (3867377 / 781250000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1579024763 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5666712511 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3681931 / 1000000000) : ℝ) ≤ √(17 / (100 * 12540) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12540) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2224914057 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39736944561 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12540) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12540) ≤ (56388101 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12540) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12540 * (162 : ℝ) ^ 2 + 26 / (10 * 12540) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12540) : ℝ)) (tA 12540 * 162 ^ 2 + 26 / (10 * 12540)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3681931 / 1000000000))) * ((3867377 / 781250000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3681931 / 1000000000)) ^ 3) * ((1579024763 / 1000000000000000000000000))) + ((5666712511 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3681931 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12540) : ℝ)) d.D d.V d.P (√(tA 12540) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3681931 / 1000000000)) ^ 2 * (((2224914057 / 1000000000000000)) * ((39736944561 / 1000000000000000000)))) + ((5666712511 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12540) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3681931 / 1000000000)) * ((3867377 / 781250000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12540) : ℝ)) (tA 12540 * 162 ^ 2 + 26 / (10 * 12540)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((3867377 / 781250000000000000) : ℝ) + (24198 / 100000) / (2 * ((3681931 / 1000000000)) ^ 2) * ((1579024763 / 1000000000000000000000000)) + ((5666712511 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12540) : ℝ)) (√(26 / (10 * 12540) : ℝ)) d.D d.V d.P (√(tA 12540) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3681931 / 1000000000)) * (((2224914057 / 1000000000000000)) * ((39736944561 / 1000000000000000000))) + ((5666712511 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12540) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((3867377 / 781250000000000000) : ℝ) + ((5666712511 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12540

namespace BstLean.Part266.Row12540
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12540 162 ∧
    0 ≤ (tableEnvelope C).f1 12540 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12540 162 ∧
    0 ≤ (tableEnvelope C).w1 12540 162 ∧ 0 ≤ (tableEnvelope C).w2 12540 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12540 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12540 162 ∧ 0 ≤ d.f1 12540 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12540 162 ∧ 0 ≤ d.w1 12540 162 ∧ 0 ≤ d.w2 12540 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12540 ≤ 2 * (228 / 100 : ℝ) / 12540 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12540 ≤ 2 * (370 / 100 : ℝ) / 12540 := by
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
    (completeRAData (tableEnvelope C) 12540 162).locationBound 12540 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12540 162).energyBound 12540 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12540 162) (d.f1 12540 162) d.f2 ≤
      32 * (((4730292053 / 1000000000000000000) : ℝ) + (789052791 / 500000000000000000) + (18964913 / 50000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12540 162) (d.w1 12540 162)
      (d.w2 12540 162) ≤
      32 * (((1904272551 / 100000000000000000000) : ℝ) + (677426777 / 50000000000000000000) + (247514873 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12540 162) (d.f1 12540 162) d.f2 ≤
      ((4730292053 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4730292053 / 1000000000000000000)) * ((789052791 / 500000000000000000)) * (126 / 100) +
      2 * (((789052791 / 500000000000000000)) ^ 2 + 2 * ((4730292053 / 1000000000000000000)) * ((18964913 / 50000000000000000))) +
      6 * ((789052791 / 500000000000000000)) * ((18964913 / 50000000000000000)) * (126 / 100) + 8 * ((18964913 / 50000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12540 162) (d.f1 12540 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12540 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12540 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12540 162) (d.f1 12540 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12540 162) (d.w1 12540 162) (d.w2 12540 162)
  have hwexpr0 : 0 ≤ d.w0 12540 162 + d.w1 12540 162 * √(π / 2) +
      2 * d.w2 12540 162 + energyR16 12540 *
      radiusPolynomialRoot16 (d.w0 12540 162) (d.w1 12540 162) (d.w2 12540 162) := by
    positivity
  constructor
  · change (12540 : ℝ) ^ 8 * (mA 12540 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12540 162) (d.f1 12540 162) d.f2 + locationR16 12540 *
        radiusPolynomialRoot16 (d.f0 12540 162) (d.f1 12540 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12540 : ℝ) ^ 8 * (mA 12540 : ℝ) ^ 8 *
        ((((4730292053 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4730292053 / 1000000000000000000)) * ((789052791 / 500000000000000000)) * (126 / 100) +
          2 * (((789052791 / 500000000000000000)) ^ 2 + 2 * ((4730292053 / 1000000000000000000)) * ((18964913 / 50000000000000000))) +
          6 * ((789052791 / 500000000000000000)) * ((18964913 / 50000000000000000)) * (126 / 100) + 8 * ((18964913 / 50000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12540) *
          (32 * (((4730292053 / 1000000000000000000) : ℝ) + (789052791 / 500000000000000000) + (18964913 / 50000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12540 : ℝ) ^ 16 *
      (d.w0 12540 162 + d.w1 12540 162 * √(π / 2) + 2 * d.w2 12540 162 +
        energyR16 12540 * radiusPolynomialRoot16 (d.w0 12540 162) (d.w1 12540 162)
          (d.w2 12540 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12540 : ℝ) ^ 16 *
        (((1904272551 / 100000000000000000000) : ℝ) + ((677426777 / 50000000000000000000)) * (126 / 100) + 2 * ((247514873 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12540) *
          (32 * (((1904272551 / 100000000000000000000) : ℝ) + (677426777 / 50000000000000000000) + (247514873 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12540

/-! A coarse bound on the actual paper statistics constant at dimension 12541. -/
namespace BstLean.Part266.Row12541
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12539 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12539 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12539 128 ≤ (12793 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12793 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12541) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12541 : ℕ))
    (by norm_num : (12541 : ℕ) ≤ 16384)
  have ht : paperTail256 12541 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12541 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12541 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12541 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12541 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12541 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12539 128 * √(2 / (12541 : ℝ)) *
      (√(12541 : ℝ) + paperT0 12541 + paperTail256 12541) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12541 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12541 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12541 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12539 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12539 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12541 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12541

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12541
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12541 (61 / 100) 162 (17 / (100 * 12541)) (26 / (10 * 12541)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12541 (61 / 100) 162 (17 / (100 * 12541)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (247452921 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1578521167 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5663063029 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12541 / 12541 * (61 / 100)) ^ 4 * inverseRadius8 (12541 - 1) /
            envelopeGap 12541 (61 / 100) 162 (17 / (100 * 12541)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12541

namespace BstLean.Part266.Row12541
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12541 162 ≤ (4729349829 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12541 162 ≤ (394447791 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (379222669 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12541 162 ≤ (380763437 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12541 162 ≤ (270905907 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12541 162 ≤ (15465979 / 3125000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (247452921 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (247452921 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1578521167 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5663063029 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((460223 / 125000000) : ℝ) ≤ √(17 / (100 * 12541) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12541) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (556161983 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19865303717 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12541) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12541) ≤ (112767209 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12541) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12541 * (162 : ℝ) ^ 2 + 26 / (10 * 12541) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12541) : ℝ)) (tA 12541 * 162 ^ 2 + 26 / (10 * 12541)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((460223 / 125000000))) * ((247452921 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((460223 / 125000000)) ^ 3) * ((1578521167 / 1000000000000000000000000))) + ((5663063029 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((460223 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12541) : ℝ)) d.D d.V d.P (√(tA 12541) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((460223 / 125000000)) ^ 2 * (((556161983 / 250000000000000)) * ((19865303717 / 500000000000000000)))) + ((5663063029 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12541) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((460223 / 125000000)) * ((247452921 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12541) : ℝ)) (tA 12541 * 162 ^ 2 + 26 / (10 * 12541)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((247452921 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((460223 / 125000000)) ^ 2) * ((1578521167 / 1000000000000000000000000)) + ((5663063029 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12541) : ℝ)) (√(26 / (10 * 12541) : ℝ)) d.D d.V d.P (√(tA 12541) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((460223 / 125000000)) * (((556161983 / 250000000000000)) * ((19865303717 / 500000000000000000))) + ((5663063029 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12541) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((247452921 / 50000000000000000000) : ℝ) + ((5663063029 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12541

namespace BstLean.Part266.Row12541
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12541 162 ∧
    0 ≤ (tableEnvelope C).f1 12541 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12541 162 ∧
    0 ≤ (tableEnvelope C).w1 12541 162 ∧ 0 ≤ (tableEnvelope C).w2 12541 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12541 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12541 162 ∧ 0 ≤ d.f1 12541 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12541 162 ∧ 0 ≤ d.w1 12541 162 ∧ 0 ≤ d.w2 12541 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12541 ≤ 2 * (228 / 100 : ℝ) / 12541 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12541 ≤ 2 * (370 / 100 : ℝ) / 12541 := by
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
    (completeRAData (tableEnvelope C) 12541 162).locationBound 12541 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12541 162).energyBound 12541 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12541 162) (d.f1 12541 162) d.f2 ≤
      32 * (((4729349829 / 1000000000000000000) : ℝ) + (394447791 / 250000000000000000) + (379222669 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12541 162) (d.w1 12541 162)
      (d.w2 12541 162) ≤
      32 * (((380763437 / 20000000000000000000) : ℝ) + (270905907 / 20000000000000000000) + (15465979 / 3125000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12541 162) (d.f1 12541 162) d.f2 ≤
      ((4729349829 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4729349829 / 1000000000000000000)) * ((394447791 / 250000000000000000)) * (126 / 100) +
      2 * (((394447791 / 250000000000000000)) ^ 2 + 2 * ((4729349829 / 1000000000000000000)) * ((379222669 / 1000000000000000000))) +
      6 * ((394447791 / 250000000000000000)) * ((379222669 / 1000000000000000000)) * (126 / 100) + 8 * ((379222669 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12541 162) (d.f1 12541 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12541 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12541 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12541 162) (d.f1 12541 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12541 162) (d.w1 12541 162) (d.w2 12541 162)
  have hwexpr0 : 0 ≤ d.w0 12541 162 + d.w1 12541 162 * √(π / 2) +
      2 * d.w2 12541 162 + energyR16 12541 *
      radiusPolynomialRoot16 (d.w0 12541 162) (d.w1 12541 162) (d.w2 12541 162) := by
    positivity
  constructor
  · change (12541 : ℝ) ^ 8 * (mA 12541 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12541 162) (d.f1 12541 162) d.f2 + locationR16 12541 *
        radiusPolynomialRoot16 (d.f0 12541 162) (d.f1 12541 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12541 : ℝ) ^ 8 * (mA 12541 : ℝ) ^ 8 *
        ((((4729349829 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4729349829 / 1000000000000000000)) * ((394447791 / 250000000000000000)) * (126 / 100) +
          2 * (((394447791 / 250000000000000000)) ^ 2 + 2 * ((4729349829 / 1000000000000000000)) * ((379222669 / 1000000000000000000))) +
          6 * ((394447791 / 250000000000000000)) * ((379222669 / 1000000000000000000)) * (126 / 100) + 8 * ((379222669 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12541) *
          (32 * (((4729349829 / 1000000000000000000) : ℝ) + (394447791 / 250000000000000000) + (379222669 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12541 : ℝ) ^ 16 *
      (d.w0 12541 162 + d.w1 12541 162 * √(π / 2) + 2 * d.w2 12541 162 +
        energyR16 12541 * radiusPolynomialRoot16 (d.w0 12541 162) (d.w1 12541 162)
          (d.w2 12541 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12541 : ℝ) ^ 16 *
        (((380763437 / 20000000000000000000) : ℝ) + ((270905907 / 20000000000000000000)) * (126 / 100) + 2 * ((15465979 / 3125000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12541) *
          (32 * (((380763437 / 20000000000000000000) : ℝ) + (270905907 / 20000000000000000000) + (15465979 / 3125000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12541

/-! A coarse bound on the actual paper statistics constant at dimension 12542. -/
namespace BstLean.Part266.Row12542
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12540 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12540 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12540 128 ≤ (12794 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12794 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12542) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12542 : ℕ))
    (by norm_num : (12542 : ℕ) ≤ 16384)
  have ht : paperTail256 12542 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12542 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12542 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12542 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12542 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12542 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12540 128 * √(2 / (12542 : ℝ)) *
      (√(12542 : ℝ) + paperT0 12542 + paperTail256 12542) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12542 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12542 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12542 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12540 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12540 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12542 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12542

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12542
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12542 (61 / 100) 162 (17 / (100 * 12542)) (26 / (10 * 12542)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12542 (61 / 100) 162 (17 / (100 * 12542)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (98957493 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (394504443 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5659416193 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12542 / 12542 * (61 / 100)) ^ 4 * inverseRadius8 (12542 - 1) /
            envelopeGap 12542 (61 / 100) 162 (17 / (100 * 12542)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12542

namespace BstLean.Part266.Row12542
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12542 162 ≤ (2364203967 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12542 162 ≤ (98592303 / 62500000000000000)
  f2 : (tableEnvelope C).f2 ≤ (3791471 / 10000000000000000)
  w0 : (tableEnvelope C).w0 12542 162 ≤ (951680989 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12542 162 ≤ (169275703 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 12542 162 ≤ (123698237 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (98957493 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (98957493 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (394504443 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5659416193 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3681637 / 1000000000) : ℝ) ≤ √(17 / (100 * 12542) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12542) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1112190929 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1588970873 / 40000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12542) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12542) ≤ (56379109 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12542) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12542 * (162 : ℝ) ^ 2 + 26 / (10 * 12542) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12542) : ℝ)) (tA 12542 * 162 ^ 2 + 26 / (10 * 12542)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3681637 / 1000000000))) * ((98957493 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3681637 / 1000000000)) ^ 3) * ((394504443 / 250000000000000000000000))) + ((5659416193 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3681637 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12542) : ℝ)) d.D d.V d.P (√(tA 12542) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3681637 / 1000000000)) ^ 2 * (((1112190929 / 500000000000000)) * ((1588970873 / 40000000000000000)))) + ((5659416193 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12542) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3681637 / 1000000000)) * ((98957493 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12542) : ℝ)) (tA 12542 * 162 ^ 2 + 26 / (10 * 12542)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((98957493 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3681637 / 1000000000)) ^ 2) * ((394504443 / 250000000000000000000000)) + ((5659416193 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12542) : ℝ)) (√(26 / (10 * 12542) : ℝ)) d.D d.V d.P (√(tA 12542) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3681637 / 1000000000)) * (((1112190929 / 500000000000000)) * ((1588970873 / 40000000000000000))) + ((5659416193 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12542) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((98957493 / 20000000000000000000) : ℝ) + ((5659416193 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12542

namespace BstLean.Part266.Row12542
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12542 162 ∧
    0 ≤ (tableEnvelope C).f1 12542 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12542 162 ∧
    0 ≤ (tableEnvelope C).w1 12542 162 ∧ 0 ≤ (tableEnvelope C).w2 12542 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12542 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12542 162 ∧ 0 ≤ d.f1 12542 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12542 162 ∧ 0 ≤ d.w1 12542 162 ∧ 0 ≤ d.w2 12542 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12542 ≤ 2 * (228 / 100 : ℝ) / 12542 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12542 ≤ 2 * (370 / 100 : ℝ) / 12542 := by
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
    (completeRAData (tableEnvelope C) 12542 162).locationBound 12542 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12542 162).energyBound 12542 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12542 162) (d.f1 12542 162) d.f2 ≤
      32 * (((2364203967 / 500000000000000000) : ℝ) + (98592303 / 62500000000000000) + (3791471 / 10000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12542 162) (d.w1 12542 162)
      (d.w2 12542 162) ≤
      32 * (((951680989 / 50000000000000000000) : ℝ) + (169275703 / 12500000000000000000) + (123698237 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12542 162) (d.f1 12542 162) d.f2 ≤
      ((2364203967 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2364203967 / 500000000000000000)) * ((98592303 / 62500000000000000)) * (126 / 100) +
      2 * (((98592303 / 62500000000000000)) ^ 2 + 2 * ((2364203967 / 500000000000000000)) * ((3791471 / 10000000000000000))) +
      6 * ((98592303 / 62500000000000000)) * ((3791471 / 10000000000000000)) * (126 / 100) + 8 * ((3791471 / 10000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12542 162) (d.f1 12542 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12542 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12542 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12542 162) (d.f1 12542 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12542 162) (d.w1 12542 162) (d.w2 12542 162)
  have hwexpr0 : 0 ≤ d.w0 12542 162 + d.w1 12542 162 * √(π / 2) +
      2 * d.w2 12542 162 + energyR16 12542 *
      radiusPolynomialRoot16 (d.w0 12542 162) (d.w1 12542 162) (d.w2 12542 162) := by
    positivity
  constructor
  · change (12542 : ℝ) ^ 8 * (mA 12542 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12542 162) (d.f1 12542 162) d.f2 + locationR16 12542 *
        radiusPolynomialRoot16 (d.f0 12542 162) (d.f1 12542 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12542 : ℝ) ^ 8 * (mA 12542 : ℝ) ^ 8 *
        ((((2364203967 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2364203967 / 500000000000000000)) * ((98592303 / 62500000000000000)) * (126 / 100) +
          2 * (((98592303 / 62500000000000000)) ^ 2 + 2 * ((2364203967 / 500000000000000000)) * ((3791471 / 10000000000000000))) +
          6 * ((98592303 / 62500000000000000)) * ((3791471 / 10000000000000000)) * (126 / 100) + 8 * ((3791471 / 10000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12542) *
          (32 * (((2364203967 / 500000000000000000) : ℝ) + (98592303 / 62500000000000000) + (3791471 / 10000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12542 : ℝ) ^ 16 *
      (d.w0 12542 162 + d.w1 12542 162 * √(π / 2) + 2 * d.w2 12542 162 +
        energyR16 12542 * radiusPolynomialRoot16 (d.w0 12542 162) (d.w1 12542 162)
          (d.w2 12542 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12542 : ℝ) ^ 16 *
        (((951680989 / 50000000000000000000) : ℝ) + ((169275703 / 12500000000000000000)) * (126 / 100) + 2 * ((123698237 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12542) *
          (32 * (((951680989 / 50000000000000000000) : ℝ) + (169275703 / 12500000000000000000) + (123698237 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12542

/-! A coarse bound on the actual paper statistics constant at dimension 12543. -/
namespace BstLean.Part266.Row12543
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12541 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12541 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12541 128 ≤ (12795 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12795 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12543) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12543 : ℕ))
    (by norm_num : (12543 : ℕ) ≤ 16384)
  have ht : paperTail256 12543 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12543 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12543 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12543 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12543 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12543 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12541 128 * √(2 / (12543 : ℝ)) *
      (√(12543 : ℝ) + paperT0 12543 + paperTail256 12543) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12543 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12543 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12543 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12541 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12541 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12543 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12543

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12543
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12543 (61 / 100) 162 (17 / (100 * 12543)) (26 / (10 * 12543)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12543 (61 / 100) 162 (17 / (100 * 12543)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (247334563 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (788757289 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2827886001 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12543 / 12543 * (61 / 100)) ^ 4 * inverseRadius8 (12543 - 1) /
            envelopeGap 12543 (61 / 100) 162 (17 / (100 * 12543)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12543

namespace BstLean.Part266.Row12543
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12543 162 ≤ (2363731331 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12543 162 ≤ (788580889 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (379071451 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12543 162 ≤ (380581233 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12543 162 ≤ (84617591 / 6250000000000000000)
  w2 : (tableEnvelope C).w2 12543 162 ≤ (98934921 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (247334563 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (247334563 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (788757289 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2827886001 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3681491 / 1000000000) : ℝ) ≤ √(17 / (100 * 12543) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12543) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1112057919 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4964742217 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12543) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12543) ≤ (28187307 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12543) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12543 * (162 : ℝ) ^ 2 + 26 / (10 * 12543) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12543) : ℝ)) (tA 12543 * 162 ^ 2 + 26 / (10 * 12543)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3681491 / 1000000000))) * ((247334563 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3681491 / 1000000000)) ^ 3) * ((788757289 / 500000000000000000000000))) + ((2827886001 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3681491 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12543) : ℝ)) d.D d.V d.P (√(tA 12543) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3681491 / 1000000000)) ^ 2 * (((1112057919 / 500000000000000)) * ((4964742217 / 125000000000000000)))) + ((2827886001 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12543) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3681491 / 1000000000)) * ((247334563 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12543) : ℝ)) (tA 12543 * 162 ^ 2 + 26 / (10 * 12543)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((247334563 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3681491 / 1000000000)) ^ 2) * ((788757289 / 500000000000000000000000)) + ((2827886001 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12543) : ℝ)) (√(26 / (10 * 12543) : ℝ)) d.D d.V d.P (√(tA 12543) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3681491 / 1000000000)) * (((1112057919 / 500000000000000)) * ((4964742217 / 125000000000000000))) + ((2827886001 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12543) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((247334563 / 50000000000000000000) : ℝ) + ((2827886001 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12543

namespace BstLean.Part266.Row12543
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12543 162 ∧
    0 ≤ (tableEnvelope C).f1 12543 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12543 162 ∧
    0 ≤ (tableEnvelope C).w1 12543 162 ∧ 0 ≤ (tableEnvelope C).w2 12543 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12543 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12543 162 ∧ 0 ≤ d.f1 12543 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12543 162 ∧ 0 ≤ d.w1 12543 162 ∧ 0 ≤ d.w2 12543 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12543 ≤ 2 * (228 / 100 : ℝ) / 12543 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12543 ≤ 2 * (370 / 100 : ℝ) / 12543 := by
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
    (completeRAData (tableEnvelope C) 12543 162).locationBound 12543 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12543 162).energyBound 12543 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12543 162) (d.f1 12543 162) d.f2 ≤
      32 * (((2363731331 / 500000000000000000) : ℝ) + (788580889 / 500000000000000000) + (379071451 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12543 162) (d.w1 12543 162)
      (d.w2 12543 162) ≤
      32 * (((380581233 / 20000000000000000000) : ℝ) + (84617591 / 6250000000000000000) + (98934921 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12543 162) (d.f1 12543 162) d.f2 ≤
      ((2363731331 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2363731331 / 500000000000000000)) * ((788580889 / 500000000000000000)) * (126 / 100) +
      2 * (((788580889 / 500000000000000000)) ^ 2 + 2 * ((2363731331 / 500000000000000000)) * ((379071451 / 1000000000000000000))) +
      6 * ((788580889 / 500000000000000000)) * ((379071451 / 1000000000000000000)) * (126 / 100) + 8 * ((379071451 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12543 162) (d.f1 12543 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12543 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12543 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12543 162) (d.f1 12543 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12543 162) (d.w1 12543 162) (d.w2 12543 162)
  have hwexpr0 : 0 ≤ d.w0 12543 162 + d.w1 12543 162 * √(π / 2) +
      2 * d.w2 12543 162 + energyR16 12543 *
      radiusPolynomialRoot16 (d.w0 12543 162) (d.w1 12543 162) (d.w2 12543 162) := by
    positivity
  constructor
  · change (12543 : ℝ) ^ 8 * (mA 12543 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12543 162) (d.f1 12543 162) d.f2 + locationR16 12543 *
        radiusPolynomialRoot16 (d.f0 12543 162) (d.f1 12543 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12543 : ℝ) ^ 8 * (mA 12543 : ℝ) ^ 8 *
        ((((2363731331 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2363731331 / 500000000000000000)) * ((788580889 / 500000000000000000)) * (126 / 100) +
          2 * (((788580889 / 500000000000000000)) ^ 2 + 2 * ((2363731331 / 500000000000000000)) * ((379071451 / 1000000000000000000))) +
          6 * ((788580889 / 500000000000000000)) * ((379071451 / 1000000000000000000)) * (126 / 100) + 8 * ((379071451 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12543) *
          (32 * (((2363731331 / 500000000000000000) : ℝ) + (788580889 / 500000000000000000) + (379071451 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12543 : ℝ) ^ 16 *
      (d.w0 12543 162 + d.w1 12543 162 * √(π / 2) + 2 * d.w2 12543 162 +
        energyR16 12543 * radiusPolynomialRoot16 (d.w0 12543 162) (d.w1 12543 162)
          (d.w2 12543 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12543 : ℝ) ^ 16 *
        (((380581233 / 20000000000000000000) : ℝ) + ((84617591 / 6250000000000000000)) * (126 / 100) + 2 * ((98934921 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12543) *
          (32 * (((380581233 / 20000000000000000000) : ℝ) + (84617591 / 6250000000000000000) + (98934921 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12543

/-! A coarse bound on the actual paper statistics constant at dimension 12544. -/
namespace BstLean.Part266.Row12544
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12542 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12542 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12542 128 ≤ (12796 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12796 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12544) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12544 : ℕ))
    (by norm_num : (12544 : ℕ) ≤ 16384)
  have ht : paperTail256 12544 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12544 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12544 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12544 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12544 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12544 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12542 128 * √(2 / (12544 : ℝ)) *
      (√(12544 : ℝ) + paperT0 12544 + paperTail256 12544) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12544 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12544 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12544 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12542 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12542 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12544 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12544

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12544
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12544 (61 / 100) 162 (17 / (100 * 12544)) (26 / (10 * 12544)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12544 (61 / 100) 162 (17 / (100 * 12544)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (19782033 / 4000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (12320403 / 7812500000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5652130453 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12544 / 12544 * (61 / 100)) ^ 4 * inverseRadius8 (12544 - 1) /
            envelopeGap 12544 (61 / 100) 162 (17 / (100 * 12544)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12544

namespace BstLean.Part266.Row12544
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12544 162 ≤ (4726521423 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12544 162 ≤ (1576847669 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (378995929 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12544 162 ≤ (76098051 / 4000000000000000000)
  w1 : (tableEnvelope C).w1 12544 162 ≤ (1353557767 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12544 162 ≤ (494556301 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (19782033 / 4000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (19782033 / 4000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (12320403 / 7812500000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5652130453 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((57521 / 15625000) : ℝ) ≤ √(17 / (100 * 12544) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12544) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (138990617 / 62500000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9927901289 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12544) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12544) ≤ (1409253 / 12500000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12544) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12544 * (162 : ℝ) ^ 2 + 26 / (10 * 12544) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12544) : ℝ)) (tA 12544 * 162 ^ 2 + 26 / (10 * 12544)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((57521 / 15625000))) * ((19782033 / 4000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((57521 / 15625000)) ^ 3) * ((12320403 / 7812500000000000000000))) + ((5652130453 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((57521 / 15625000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12544) : ℝ)) d.D d.V d.P (√(tA 12544) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((57521 / 15625000)) ^ 2 * (((138990617 / 62500000000000)) * ((9927901289 / 250000000000000000)))) + ((5652130453 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12544) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((57521 / 15625000)) * ((19782033 / 4000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12544) : ℝ)) (tA 12544 * 162 ^ 2 + 26 / (10 * 12544)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((19782033 / 4000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((57521 / 15625000)) ^ 2) * ((12320403 / 7812500000000000000000)) + ((5652130453 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12544) : ℝ)) (√(26 / (10 * 12544) : ℝ)) d.D d.V d.P (√(tA 12544) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((57521 / 15625000)) * (((138990617 / 62500000000000)) * ((9927901289 / 250000000000000000))) + ((5652130453 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12544) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((19782033 / 4000000000000000000) : ℝ) + ((5652130453 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12544

namespace BstLean.Part266.Row12544
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12544 162 ∧
    0 ≤ (tableEnvelope C).f1 12544 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12544 162 ∧
    0 ≤ (tableEnvelope C).w1 12544 162 ∧ 0 ≤ (tableEnvelope C).w2 12544 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12544 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12544 162 ∧ 0 ≤ d.f1 12544 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12544 162 ∧ 0 ≤ d.w1 12544 162 ∧ 0 ≤ d.w2 12544 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12544 ≤ 2 * (228 / 100 : ℝ) / 12544 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12544 ≤ 2 * (370 / 100 : ℝ) / 12544 := by
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
    (completeRAData (tableEnvelope C) 12544 162).locationBound 12544 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12544 162).energyBound 12544 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12544 162) (d.f1 12544 162) d.f2 ≤
      32 * (((4726521423 / 1000000000000000000) : ℝ) + (1576847669 / 1000000000000000000) + (378995929 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12544 162) (d.w1 12544 162)
      (d.w2 12544 162) ≤
      32 * (((76098051 / 4000000000000000000) : ℝ) + (1353557767 / 100000000000000000000) + (494556301 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12544 162) (d.f1 12544 162) d.f2 ≤
      ((4726521423 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4726521423 / 1000000000000000000)) * ((1576847669 / 1000000000000000000)) * (126 / 100) +
      2 * (((1576847669 / 1000000000000000000)) ^ 2 + 2 * ((4726521423 / 1000000000000000000)) * ((378995929 / 1000000000000000000))) +
      6 * ((1576847669 / 1000000000000000000)) * ((378995929 / 1000000000000000000)) * (126 / 100) + 8 * ((378995929 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12544 162) (d.f1 12544 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12544 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12544 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12544 162) (d.f1 12544 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12544 162) (d.w1 12544 162) (d.w2 12544 162)
  have hwexpr0 : 0 ≤ d.w0 12544 162 + d.w1 12544 162 * √(π / 2) +
      2 * d.w2 12544 162 + energyR16 12544 *
      radiusPolynomialRoot16 (d.w0 12544 162) (d.w1 12544 162) (d.w2 12544 162) := by
    positivity
  constructor
  · change (12544 : ℝ) ^ 8 * (mA 12544 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12544 162) (d.f1 12544 162) d.f2 + locationR16 12544 *
        radiusPolynomialRoot16 (d.f0 12544 162) (d.f1 12544 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12544 : ℝ) ^ 8 * (mA 12544 : ℝ) ^ 8 *
        ((((4726521423 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4726521423 / 1000000000000000000)) * ((1576847669 / 1000000000000000000)) * (126 / 100) +
          2 * (((1576847669 / 1000000000000000000)) ^ 2 + 2 * ((4726521423 / 1000000000000000000)) * ((378995929 / 1000000000000000000))) +
          6 * ((1576847669 / 1000000000000000000)) * ((378995929 / 1000000000000000000)) * (126 / 100) + 8 * ((378995929 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12544) *
          (32 * (((4726521423 / 1000000000000000000) : ℝ) + (1576847669 / 1000000000000000000) + (378995929 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12544 : ℝ) ^ 16 *
      (d.w0 12544 162 + d.w1 12544 162 * √(π / 2) + 2 * d.w2 12544 162 +
        energyR16 12544 * radiusPolynomialRoot16 (d.w0 12544 162) (d.w1 12544 162)
          (d.w2 12544 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12544 : ℝ) ^ 16 *
        (((76098051 / 4000000000000000000) : ℝ) + ((1353557767 / 100000000000000000000)) * (126 / 100) + 2 * ((494556301 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12544) *
          (32 * (((76098051 / 4000000000000000000) : ℝ) + (1353557767 / 100000000000000000000) + (494556301 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12544

/-! A coarse bound on the actual paper statistics constant at dimension 12545. -/
namespace BstLean.Part266.Row12545
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12543 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12543 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12543 128 ≤ (12797 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12797 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12545) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12545 : ℕ))
    (by norm_num : (12545 : ℕ) ≤ 16384)
  have ht : paperTail256 12545 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12545 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12545 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12545 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12545 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12545 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12543 128 * √(2 / (12545 : ℝ)) *
      (√(12545 : ℝ) + paperT0 12545 + paperTail256 12545) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12545 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12545 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12545 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12543 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12543 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12545 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12545

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12545
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12545 (61 / 100) 162 (17 / (100 * 12545)) (26 / (10 * 12545)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12545 (61 / 100) 162 (17 / (100 * 12545)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (247216281 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (157650879 / 100000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (706061443 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12545 / 12545 * (61 / 100)) ^ 4 * inverseRadius8 (12545 - 1) /
            envelopeGap 12545 (61 / 100) 162 (17 / (100 * 12545)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12545

namespace BstLean.Part266.Row12545
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12545 162 ≤ (472558051 / 100000000000000000)
  f1 : (tableEnvelope C).f1 12545 162 ≤ (1576533661 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (378920429 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12545 162 ≤ (1901996543 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12545 162 ≤ (676617093 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12545 162 ≤ (247219017 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (247216281 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (247216281 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (157650879 / 100000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (706061443 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3681197 / 1000000000) : ℝ) ≤ √(17 / (100 * 12545) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12545) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2223583959 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39705274083 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12545) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12545) ≤ (112731253 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12545) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12545 * (162 : ℝ) ^ 2 + 26 / (10 * 12545) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12545) : ℝ)) (tA 12545 * 162 ^ 2 + 26 / (10 * 12545)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3681197 / 1000000000))) * ((247216281 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3681197 / 1000000000)) ^ 3) * ((157650879 / 100000000000000000000000))) + ((706061443 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3681197 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12545) : ℝ)) d.D d.V d.P (√(tA 12545) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3681197 / 1000000000)) ^ 2 * (((2223583959 / 1000000000000000)) * ((39705274083 / 1000000000000000000)))) + ((706061443 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12545) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3681197 / 1000000000)) * ((247216281 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12545) : ℝ)) (tA 12545 * 162 ^ 2 + 26 / (10 * 12545)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((247216281 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3681197 / 1000000000)) ^ 2) * ((157650879 / 100000000000000000000000)) + ((706061443 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12545) : ℝ)) (√(26 / (10 * 12545) : ℝ)) d.D d.V d.P (√(tA 12545) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3681197 / 1000000000)) * (((2223583959 / 1000000000000000)) * ((39705274083 / 1000000000000000000))) + ((706061443 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12545) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((247216281 / 50000000000000000000) : ℝ) + ((706061443 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12545

namespace BstLean.Part266.Row12545
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12545 162 ∧
    0 ≤ (tableEnvelope C).f1 12545 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12545 162 ∧
    0 ≤ (tableEnvelope C).w1 12545 162 ∧ 0 ≤ (tableEnvelope C).w2 12545 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12545 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12545 162 ∧ 0 ≤ d.f1 12545 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12545 162 ∧ 0 ≤ d.w1 12545 162 ∧ 0 ≤ d.w2 12545 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12545 ≤ 2 * (228 / 100 : ℝ) / 12545 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12545 ≤ 2 * (370 / 100 : ℝ) / 12545 := by
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
    (completeRAData (tableEnvelope C) 12545 162).locationBound 12545 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12545 162).energyBound 12545 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12545 162) (d.f1 12545 162) d.f2 ≤
      32 * (((472558051 / 100000000000000000) : ℝ) + (1576533661 / 1000000000000000000) + (378920429 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12545 162) (d.w1 12545 162)
      (d.w2 12545 162) ≤
      32 * (((1901996543 / 100000000000000000000) : ℝ) + (676617093 / 50000000000000000000) + (247219017 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12545 162) (d.f1 12545 162) d.f2 ≤
      ((472558051 / 100000000000000000) : ℝ) ^ 2 + 2 * ((472558051 / 100000000000000000)) * ((1576533661 / 1000000000000000000)) * (126 / 100) +
      2 * (((1576533661 / 1000000000000000000)) ^ 2 + 2 * ((472558051 / 100000000000000000)) * ((378920429 / 1000000000000000000))) +
      6 * ((1576533661 / 1000000000000000000)) * ((378920429 / 1000000000000000000)) * (126 / 100) + 8 * ((378920429 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12545 162) (d.f1 12545 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12545 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12545 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12545 162) (d.f1 12545 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12545 162) (d.w1 12545 162) (d.w2 12545 162)
  have hwexpr0 : 0 ≤ d.w0 12545 162 + d.w1 12545 162 * √(π / 2) +
      2 * d.w2 12545 162 + energyR16 12545 *
      radiusPolynomialRoot16 (d.w0 12545 162) (d.w1 12545 162) (d.w2 12545 162) := by
    positivity
  constructor
  · change (12545 : ℝ) ^ 8 * (mA 12545 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12545 162) (d.f1 12545 162) d.f2 + locationR16 12545 *
        radiusPolynomialRoot16 (d.f0 12545 162) (d.f1 12545 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12545 : ℝ) ^ 8 * (mA 12545 : ℝ) ^ 8 *
        ((((472558051 / 100000000000000000) : ℝ) ^ 2 + 2 * ((472558051 / 100000000000000000)) * ((1576533661 / 1000000000000000000)) * (126 / 100) +
          2 * (((1576533661 / 1000000000000000000)) ^ 2 + 2 * ((472558051 / 100000000000000000)) * ((378920429 / 1000000000000000000))) +
          6 * ((1576533661 / 1000000000000000000)) * ((378920429 / 1000000000000000000)) * (126 / 100) + 8 * ((378920429 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12545) *
          (32 * (((472558051 / 100000000000000000) : ℝ) + (1576533661 / 1000000000000000000) + (378920429 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12545 : ℝ) ^ 16 *
      (d.w0 12545 162 + d.w1 12545 162 * √(π / 2) + 2 * d.w2 12545 162 +
        energyR16 12545 * radiusPolynomialRoot16 (d.w0 12545 162) (d.w1 12545 162)
          (d.w2 12545 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12545 : ℝ) ^ 16 *
        (((1901996543 / 100000000000000000000) : ℝ) + ((676617093 / 50000000000000000000)) * (126 / 100) + 2 * ((247219017 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12545) *
          (32 * (((1901996543 / 100000000000000000000) : ℝ) + (676617093 / 50000000000000000000) + (247219017 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12545

/-! A coarse bound on the actual paper statistics constant at dimension 12546. -/
namespace BstLean.Part266.Row12546
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12544 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12544 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12544 128 ≤ (12798 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12798 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12546) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12546 : ℕ))
    (by norm_num : (12546 : ℕ) ≤ 16384)
  have ht : paperTail256 12546 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12546 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12546 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12546 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12546 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12546 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12544 128 * √(2 / (12546 : ℝ)) *
      (√(12546 : ℝ) + paperT0 12546 + paperTail256 12546) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12546 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12546 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12546 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12544 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12544 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12546 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12546

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12546
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12546 (61 / 100) 162 (17 / (100 * 12546)) (26 / (10 * 12546)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12546 (61 / 100) 162 (17 / (100 * 12546)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (15447323 / 3125000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1576006197 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2822427637 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12546 / 12546 * (61 / 100)) ^ 4 * inverseRadius8 (12546 - 1) /
            envelopeGap 12546 (61 / 100) 162 (17 / (100 * 12546)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12546

namespace BstLean.Part266.Row12546
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12546 162 ≤ (2362319963 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12546 162 ≤ (394054939 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (47355619 / 125000000000000000)
  w0 : (tableEnvelope C).w0 12546 162 ≤ (190154197 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 12546 162 ≤ (676455357 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12546 162 ≤ (98863961 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (15447323 / 3125000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (15447323 / 3125000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1576006197 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2822427637 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((73621 / 20000000) : ℝ) ≤ √(17 / (100 * 12546) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12546) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2223318097 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39698944533 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12546) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12546) ≤ (28180567 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12546) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12546 * (162 : ℝ) ^ 2 + 26 / (10 * 12546) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12546) : ℝ)) (tA 12546 * 162 ^ 2 + 26 / (10 * 12546)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((73621 / 20000000))) * ((15447323 / 3125000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((73621 / 20000000)) ^ 3) * ((1576006197 / 1000000000000000000000000))) + ((2822427637 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((73621 / 20000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12546) : ℝ)) d.D d.V d.P (√(tA 12546) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((73621 / 20000000)) ^ 2 * (((2223318097 / 1000000000000000)) * ((39698944533 / 1000000000000000000)))) + ((2822427637 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12546) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((73621 / 20000000)) * ((15447323 / 3125000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12546) : ℝ)) (tA 12546 * 162 ^ 2 + 26 / (10 * 12546)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((15447323 / 3125000000000000000) : ℝ) + (24198 / 100000) / (2 * ((73621 / 20000000)) ^ 2) * ((1576006197 / 1000000000000000000000000)) + ((2822427637 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12546) : ℝ)) (√(26 / (10 * 12546) : ℝ)) d.D d.V d.P (√(tA 12546) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((73621 / 20000000)) * (((2223318097 / 1000000000000000)) * ((39698944533 / 1000000000000000000))) + ((2822427637 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12546) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((15447323 / 3125000000000000000) : ℝ) + ((2822427637 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12546

namespace BstLean.Part266.Row12546
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12546 162 ∧
    0 ≤ (tableEnvelope C).f1 12546 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12546 162 ∧
    0 ≤ (tableEnvelope C).w1 12546 162 ∧ 0 ≤ (tableEnvelope C).w2 12546 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12546 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12546 162 ∧ 0 ≤ d.f1 12546 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12546 162 ∧ 0 ≤ d.w1 12546 162 ∧ 0 ≤ d.w2 12546 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12546 ≤ 2 * (228 / 100 : ℝ) / 12546 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12546 ≤ 2 * (370 / 100 : ℝ) / 12546 := by
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
    (completeRAData (tableEnvelope C) 12546 162).locationBound 12546 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12546 162).energyBound 12546 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12546 162) (d.f1 12546 162) d.f2 ≤
      32 * (((2362319963 / 500000000000000000) : ℝ) + (394054939 / 250000000000000000) + (47355619 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12546 162) (d.w1 12546 162)
      (d.w2 12546 162) ≤
      32 * (((190154197 / 10000000000000000000) : ℝ) + (676455357 / 50000000000000000000) + (98863961 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12546 162) (d.f1 12546 162) d.f2 ≤
      ((2362319963 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2362319963 / 500000000000000000)) * ((394054939 / 250000000000000000)) * (126 / 100) +
      2 * (((394054939 / 250000000000000000)) ^ 2 + 2 * ((2362319963 / 500000000000000000)) * ((47355619 / 125000000000000000))) +
      6 * ((394054939 / 250000000000000000)) * ((47355619 / 125000000000000000)) * (126 / 100) + 8 * ((47355619 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12546 162) (d.f1 12546 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12546 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12546 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12546 162) (d.f1 12546 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12546 162) (d.w1 12546 162) (d.w2 12546 162)
  have hwexpr0 : 0 ≤ d.w0 12546 162 + d.w1 12546 162 * √(π / 2) +
      2 * d.w2 12546 162 + energyR16 12546 *
      radiusPolynomialRoot16 (d.w0 12546 162) (d.w1 12546 162) (d.w2 12546 162) := by
    positivity
  constructor
  · change (12546 : ℝ) ^ 8 * (mA 12546 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12546 162) (d.f1 12546 162) d.f2 + locationR16 12546 *
        radiusPolynomialRoot16 (d.f0 12546 162) (d.f1 12546 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12546 : ℝ) ^ 8 * (mA 12546 : ℝ) ^ 8 *
        ((((2362319963 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2362319963 / 500000000000000000)) * ((394054939 / 250000000000000000)) * (126 / 100) +
          2 * (((394054939 / 250000000000000000)) ^ 2 + 2 * ((2362319963 / 500000000000000000)) * ((47355619 / 125000000000000000))) +
          6 * ((394054939 / 250000000000000000)) * ((47355619 / 125000000000000000)) * (126 / 100) + 8 * ((47355619 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12546) *
          (32 * (((2362319963 / 500000000000000000) : ℝ) + (394054939 / 250000000000000000) + (47355619 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12546 : ℝ) ^ 16 *
      (d.w0 12546 162 + d.w1 12546 162 * √(π / 2) + 2 * d.w2 12546 162 +
        energyR16 12546 * radiusPolynomialRoot16 (d.w0 12546 162) (d.w1 12546 162)
          (d.w2 12546 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12546 : ℝ) ^ 16 *
        (((190154197 / 10000000000000000000) : ℝ) + ((676455357 / 50000000000000000000)) * (126 / 100) + 2 * ((98863961 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12546) *
          (32 * (((190154197 / 10000000000000000000) : ℝ) + (676455357 / 50000000000000000000) + (98863961 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12546

/-! A coarse bound on the actual paper statistics constant at dimension 12547. -/
namespace BstLean.Part266.Row12547
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12545 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12545 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12545 128 ≤ (12799 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12799 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12547) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12547 : ℕ))
    (by norm_num : (12547 : ℕ) ≤ 16384)
  have ht : paperTail256 12547 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12547 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12547 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12547 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12547 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12547 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12545 128 * √(2 / (12547 : ℝ)) *
      (√(12547 : ℝ) + paperT0 12547 + paperTail256 12547) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12547 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12547 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12547 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12545 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12545 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12547 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12547

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12547
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12547 (61 / 100) 162 (17 / (100 * 12547)) (26 / (10 * 12547)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12547 (61 / 100) 162 (17 / (100 * 12547)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (494196149 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (393875951 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (141030541 / 25000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12547 / 12547 * (61 / 100)) ^ 4 * inverseRadius8 (12547 - 1) /
            envelopeGap 12547 (61 / 100) 162 (17 / (100 * 12547)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12547

namespace BstLean.Part266.Row12547
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12547 162 ≤ (944739193 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12547 162 ≤ (1575905099 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (94692349 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12547 162 ≤ (237635849 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 12547 162 ≤ (1352586987 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12547 162 ≤ (247100807 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (494196149 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (494196149 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (393875951 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (141030541 / 25000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((460113 / 125000000) : ℝ) ≤ √(17 / (100 * 12547) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12547) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (555763073 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39692616493 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12547) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12547) ≤ (28178321 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12547) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12547 * (162 : ℝ) ^ 2 + 26 / (10 * 12547) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12547) : ℝ)) (tA 12547 * 162 ^ 2 + 26 / (10 * 12547)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((460113 / 125000000))) * ((494196149 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((460113 / 125000000)) ^ 3) * ((393875951 / 250000000000000000000000))) + ((141030541 / 25000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((460113 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12547) : ℝ)) d.D d.V d.P (√(tA 12547) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((460113 / 125000000)) ^ 2 * (((555763073 / 250000000000000)) * ((39692616493 / 1000000000000000000)))) + ((141030541 / 25000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12547) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((460113 / 125000000)) * ((494196149 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12547) : ℝ)) (tA 12547 * 162 ^ 2 + 26 / (10 * 12547)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((494196149 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((460113 / 125000000)) ^ 2) * ((393875951 / 250000000000000000000000)) + ((141030541 / 25000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12547) : ℝ)) (√(26 / (10 * 12547) : ℝ)) d.D d.V d.P (√(tA 12547) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((460113 / 125000000)) * (((555763073 / 250000000000000)) * ((39692616493 / 1000000000000000000))) + ((141030541 / 25000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12547) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((494196149 / 100000000000000000000) : ℝ) + ((141030541 / 25000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12547

namespace BstLean.Part266.Row12547
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12547 162 ∧
    0 ≤ (tableEnvelope C).f1 12547 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12547 162 ∧
    0 ≤ (tableEnvelope C).w1 12547 162 ∧ 0 ≤ (tableEnvelope C).w2 12547 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12547 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12547 162 ∧ 0 ≤ d.f1 12547 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12547 162 ∧ 0 ≤ d.w1 12547 162 ∧ 0 ≤ d.w2 12547 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12547 ≤ 2 * (228 / 100 : ℝ) / 12547 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12547 ≤ 2 * (370 / 100 : ℝ) / 12547 := by
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
    (completeRAData (tableEnvelope C) 12547 162).locationBound 12547 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12547 162).energyBound 12547 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12547 162) (d.f1 12547 162) d.f2 ≤
      32 * (((944739193 / 200000000000000000) : ℝ) + (1575905099 / 1000000000000000000) + (94692349 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12547 162) (d.w1 12547 162)
      (d.w2 12547 162) ≤
      32 * (((237635849 / 12500000000000000000) : ℝ) + (1352586987 / 100000000000000000000) + (247100807 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12547 162) (d.f1 12547 162) d.f2 ≤
      ((944739193 / 200000000000000000) : ℝ) ^ 2 + 2 * ((944739193 / 200000000000000000)) * ((1575905099 / 1000000000000000000)) * (126 / 100) +
      2 * (((1575905099 / 1000000000000000000)) ^ 2 + 2 * ((944739193 / 200000000000000000)) * ((94692349 / 250000000000000000))) +
      6 * ((1575905099 / 1000000000000000000)) * ((94692349 / 250000000000000000)) * (126 / 100) + 8 * ((94692349 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12547 162) (d.f1 12547 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12547 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12547 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12547 162) (d.f1 12547 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12547 162) (d.w1 12547 162) (d.w2 12547 162)
  have hwexpr0 : 0 ≤ d.w0 12547 162 + d.w1 12547 162 * √(π / 2) +
      2 * d.w2 12547 162 + energyR16 12547 *
      radiusPolynomialRoot16 (d.w0 12547 162) (d.w1 12547 162) (d.w2 12547 162) := by
    positivity
  constructor
  · change (12547 : ℝ) ^ 8 * (mA 12547 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12547 162) (d.f1 12547 162) d.f2 + locationR16 12547 *
        radiusPolynomialRoot16 (d.f0 12547 162) (d.f1 12547 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12547 : ℝ) ^ 8 * (mA 12547 : ℝ) ^ 8 *
        ((((944739193 / 200000000000000000) : ℝ) ^ 2 + 2 * ((944739193 / 200000000000000000)) * ((1575905099 / 1000000000000000000)) * (126 / 100) +
          2 * (((1575905099 / 1000000000000000000)) ^ 2 + 2 * ((944739193 / 200000000000000000)) * ((94692349 / 250000000000000000))) +
          6 * ((1575905099 / 1000000000000000000)) * ((94692349 / 250000000000000000)) * (126 / 100) + 8 * ((94692349 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12547) *
          (32 * (((944739193 / 200000000000000000) : ℝ) + (1575905099 / 1000000000000000000) + (94692349 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12547 : ℝ) ^ 16 *
      (d.w0 12547 162 + d.w1 12547 162 * √(π / 2) + 2 * d.w2 12547 162 +
        energyR16 12547 * radiusPolynomialRoot16 (d.w0 12547 162) (d.w1 12547 162)
          (d.w2 12547 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12547 : ℝ) ^ 16 *
        (((237635849 / 12500000000000000000) : ℝ) + ((1352586987 / 100000000000000000000)) * (126 / 100) + 2 * ((247100807 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12547) *
          (32 * (((237635849 / 12500000000000000000) : ℝ) + (1352586987 / 100000000000000000000) + (247100807 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12547

/-! A coarse bound on the actual paper statistics constant at dimension 12548. -/
namespace BstLean.Part266.Row12548
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12546 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12546 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12546 128 ≤ (12800 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12800 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12548) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12548 : ℕ))
    (by norm_num : (12548 : ℕ) ≤ 16384)
  have ht : paperTail256 12548 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12548 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12548 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12548 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12548 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12548 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12546 128 * √(2 / (12548 : ℝ)) *
      (√(12548 : ℝ) + paperT0 12548 + paperTail256 12548) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12548 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12548 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12548 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12546 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12546 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12548 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12548

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12548
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12548 (61 / 100) 162 (17 / (100 * 12548)) (26 / (10 * 12548)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12548 (61 / 100) 162 (17 / (100 * 12548)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (247038999 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (393750403 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5637590639 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12548 / 12548 * (61 / 100)) ^ 4 * inverseRadius8 (12548 - 1) /
            envelopeGap 12548 (61 / 100) 162 (17 / (100 * 12548)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12548

namespace BstLean.Part266.Row12548
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12548 162 ≤ (2361378019 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12548 162 ≤ (1575591399 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (75738793 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12548 162 ≤ (380126507 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12548 162 ≤ (676131867 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12548 162 ≤ (24704173 / 5000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (247038999 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (247038999 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (393750403 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5637590639 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3680757 / 1000000000) : ℝ) ≤ √(17 / (100 * 12548) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12548) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (444557307 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4960786247 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12548) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12548) ≤ (112704301 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12548) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12548 * (162 : ℝ) ^ 2 + 26 / (10 * 12548) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12548) : ℝ)) (tA 12548 * 162 ^ 2 + 26 / (10 * 12548)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3680757 / 1000000000))) * ((247038999 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3680757 / 1000000000)) ^ 3) * ((393750403 / 250000000000000000000000))) + ((5637590639 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3680757 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12548) : ℝ)) d.D d.V d.P (√(tA 12548) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3680757 / 1000000000)) ^ 2 * (((444557307 / 200000000000000)) * ((4960786247 / 125000000000000000)))) + ((5637590639 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12548) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3680757 / 1000000000)) * ((247038999 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12548) : ℝ)) (tA 12548 * 162 ^ 2 + 26 / (10 * 12548)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((247038999 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3680757 / 1000000000)) ^ 2) * ((393750403 / 250000000000000000000000)) + ((5637590639 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12548) : ℝ)) (√(26 / (10 * 12548) : ℝ)) d.D d.V d.P (√(tA 12548) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3680757 / 1000000000)) * (((444557307 / 200000000000000)) * ((4960786247 / 125000000000000000))) + ((5637590639 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12548) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((247038999 / 50000000000000000000) : ℝ) + ((5637590639 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12548

namespace BstLean.Part266.Row12548
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12548 162 ∧
    0 ≤ (tableEnvelope C).f1 12548 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12548 162 ∧
    0 ≤ (tableEnvelope C).w1 12548 162 ∧ 0 ≤ (tableEnvelope C).w2 12548 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12548 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12548 162 ∧ 0 ≤ d.f1 12548 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12548 162 ∧ 0 ≤ d.w1 12548 162 ∧ 0 ≤ d.w2 12548 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12548 ≤ 2 * (228 / 100 : ℝ) / 12548 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12548 ≤ 2 * (370 / 100 : ℝ) / 12548 := by
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
    (completeRAData (tableEnvelope C) 12548 162).locationBound 12548 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12548 162).energyBound 12548 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12548 162) (d.f1 12548 162) d.f2 ≤
      32 * (((2361378019 / 500000000000000000) : ℝ) + (1575591399 / 1000000000000000000) + (75738793 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12548 162) (d.w1 12548 162)
      (d.w2 12548 162) ≤
      32 * (((380126507 / 20000000000000000000) : ℝ) + (676131867 / 50000000000000000000) + (24704173 / 5000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12548 162) (d.f1 12548 162) d.f2 ≤
      ((2361378019 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2361378019 / 500000000000000000)) * ((1575591399 / 1000000000000000000)) * (126 / 100) +
      2 * (((1575591399 / 1000000000000000000)) ^ 2 + 2 * ((2361378019 / 500000000000000000)) * ((75738793 / 200000000000000000))) +
      6 * ((1575591399 / 1000000000000000000)) * ((75738793 / 200000000000000000)) * (126 / 100) + 8 * ((75738793 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12548 162) (d.f1 12548 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12548 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12548 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12548 162) (d.f1 12548 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12548 162) (d.w1 12548 162) (d.w2 12548 162)
  have hwexpr0 : 0 ≤ d.w0 12548 162 + d.w1 12548 162 * √(π / 2) +
      2 * d.w2 12548 162 + energyR16 12548 *
      radiusPolynomialRoot16 (d.w0 12548 162) (d.w1 12548 162) (d.w2 12548 162) := by
    positivity
  constructor
  · change (12548 : ℝ) ^ 8 * (mA 12548 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12548 162) (d.f1 12548 162) d.f2 + locationR16 12548 *
        radiusPolynomialRoot16 (d.f0 12548 162) (d.f1 12548 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12548 : ℝ) ^ 8 * (mA 12548 : ℝ) ^ 8 *
        ((((2361378019 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2361378019 / 500000000000000000)) * ((1575591399 / 1000000000000000000)) * (126 / 100) +
          2 * (((1575591399 / 1000000000000000000)) ^ 2 + 2 * ((2361378019 / 500000000000000000)) * ((75738793 / 200000000000000000))) +
          6 * ((1575591399 / 1000000000000000000)) * ((75738793 / 200000000000000000)) * (126 / 100) + 8 * ((75738793 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12548) *
          (32 * (((2361378019 / 500000000000000000) : ℝ) + (1575591399 / 1000000000000000000) + (75738793 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12548 : ℝ) ^ 16 *
      (d.w0 12548 162 + d.w1 12548 162 * √(π / 2) + 2 * d.w2 12548 162 +
        energyR16 12548 * radiusPolynomialRoot16 (d.w0 12548 162) (d.w1 12548 162)
          (d.w2 12548 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12548 : ℝ) ^ 16 *
        (((380126507 / 20000000000000000000) : ℝ) + ((676131867 / 50000000000000000000)) * (126 / 100) + 2 * ((24704173 / 5000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12548) *
          (32 * (((380126507 / 20000000000000000000) : ℝ) + (676131867 / 50000000000000000000) + (24704173 / 5000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12548

/-! A coarse bound on the actual paper statistics constant at dimension 12549. -/
namespace BstLean.Part266.Row12549
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12547 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12547 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12547 128 ≤ (12801 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12801 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12549) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12549 : ℕ))
    (by norm_num : (12549 : ℕ) ≤ 16384)
  have ht : paperTail256 12549 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12549 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12549 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12549 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12549 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12549 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12547 128 * √(2 / (12549 : ℝ)) *
      (√(12549 : ℝ) + paperT0 12549 + paperTail256 12549) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12549 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12549 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12549 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12547 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12547 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12549 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12549

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12549
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12549 (61 / 100) 162 (17 / (100 * 12549)) (26 / (10 * 12549)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12549 (61 / 100) 162 (17 / (100 * 12549)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (246979943 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1574499619 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5633962271 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12549 / 12549 * (61 / 100)) ^ 4 * inverseRadius8 (12549 - 1) /
            envelopeGap 12549 (61 / 100) 162 (17 / (100 * 12549)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12549

namespace BstLean.Part266.Row12549
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12549 162 ≤ (944363287 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12549 162 ≤ (1575277803 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (378618557 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12549 162 ≤ (1900178437 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12549 162 ≤ (1351940593 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12549 162 ≤ (15436417 / 3125000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (246979943 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (246979943 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1574499619 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5633962271 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((368061 / 100000000) : ℝ) ≤ √(17 / (100 * 12549) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12549) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (444504167 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19839982479 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12549) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12549) ≤ (2817383 / 25000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12549) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12549 * (162 : ℝ) ^ 2 + 26 / (10 * 12549) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12549) : ℝ)) (tA 12549 * 162 ^ 2 + 26 / (10 * 12549)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((368061 / 100000000))) * ((246979943 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((368061 / 100000000)) ^ 3) * ((1574499619 / 1000000000000000000000000))) + ((5633962271 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((368061 / 100000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12549) : ℝ)) d.D d.V d.P (√(tA 12549) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((368061 / 100000000)) ^ 2 * (((444504167 / 200000000000000)) * ((19839982479 / 500000000000000000)))) + ((5633962271 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12549) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((368061 / 100000000)) * ((246979943 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12549) : ℝ)) (tA 12549 * 162 ^ 2 + 26 / (10 * 12549)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((246979943 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((368061 / 100000000)) ^ 2) * ((1574499619 / 1000000000000000000000000)) + ((5633962271 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12549) : ℝ)) (√(26 / (10 * 12549) : ℝ)) d.D d.V d.P (√(tA 12549) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((368061 / 100000000)) * (((444504167 / 200000000000000)) * ((19839982479 / 500000000000000000))) + ((5633962271 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12549) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((246979943 / 50000000000000000000) : ℝ) + ((5633962271 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12549

namespace BstLean.Part266.Row12549
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12549 162 ∧
    0 ≤ (tableEnvelope C).f1 12549 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12549 162 ∧
    0 ≤ (tableEnvelope C).w1 12549 162 ∧ 0 ≤ (tableEnvelope C).w2 12549 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12549 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12549 162 ∧ 0 ≤ d.f1 12549 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12549 162 ∧ 0 ≤ d.w1 12549 162 ∧ 0 ≤ d.w2 12549 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12549 ≤ 2 * (228 / 100 : ℝ) / 12549 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12549 ≤ 2 * (370 / 100 : ℝ) / 12549 := by
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
    (completeRAData (tableEnvelope C) 12549 162).locationBound 12549 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12549 162).energyBound 12549 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12549 162) (d.f1 12549 162) d.f2 ≤
      32 * (((944363287 / 200000000000000000) : ℝ) + (1575277803 / 1000000000000000000) + (378618557 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12549 162) (d.w1 12549 162)
      (d.w2 12549 162) ≤
      32 * (((1900178437 / 100000000000000000000) : ℝ) + (1351940593 / 100000000000000000000) + (15436417 / 3125000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12549 162) (d.f1 12549 162) d.f2 ≤
      ((944363287 / 200000000000000000) : ℝ) ^ 2 + 2 * ((944363287 / 200000000000000000)) * ((1575277803 / 1000000000000000000)) * (126 / 100) +
      2 * (((1575277803 / 1000000000000000000)) ^ 2 + 2 * ((944363287 / 200000000000000000)) * ((378618557 / 1000000000000000000))) +
      6 * ((1575277803 / 1000000000000000000)) * ((378618557 / 1000000000000000000)) * (126 / 100) + 8 * ((378618557 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12549 162) (d.f1 12549 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12549 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12549 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12549 162) (d.f1 12549 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12549 162) (d.w1 12549 162) (d.w2 12549 162)
  have hwexpr0 : 0 ≤ d.w0 12549 162 + d.w1 12549 162 * √(π / 2) +
      2 * d.w2 12549 162 + energyR16 12549 *
      radiusPolynomialRoot16 (d.w0 12549 162) (d.w1 12549 162) (d.w2 12549 162) := by
    positivity
  constructor
  · change (12549 : ℝ) ^ 8 * (mA 12549 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12549 162) (d.f1 12549 162) d.f2 + locationR16 12549 *
        radiusPolynomialRoot16 (d.f0 12549 162) (d.f1 12549 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12549 : ℝ) ^ 8 * (mA 12549 : ℝ) ^ 8 *
        ((((944363287 / 200000000000000000) : ℝ) ^ 2 + 2 * ((944363287 / 200000000000000000)) * ((1575277803 / 1000000000000000000)) * (126 / 100) +
          2 * (((1575277803 / 1000000000000000000)) ^ 2 + 2 * ((944363287 / 200000000000000000)) * ((378618557 / 1000000000000000000))) +
          6 * ((1575277803 / 1000000000000000000)) * ((378618557 / 1000000000000000000)) * (126 / 100) + 8 * ((378618557 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12549) *
          (32 * (((944363287 / 200000000000000000) : ℝ) + (1575277803 / 1000000000000000000) + (378618557 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12549 : ℝ) ^ 16 *
      (d.w0 12549 162 + d.w1 12549 162 * √(π / 2) + 2 * d.w2 12549 162 +
        energyR16 12549 * radiusPolynomialRoot16 (d.w0 12549 162) (d.w1 12549 162)
          (d.w2 12549 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12549 : ℝ) ^ 16 *
        (((1900178437 / 100000000000000000000) : ℝ) + ((1351940593 / 100000000000000000000)) * (126 / 100) + 2 * ((15436417 / 3125000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12549) *
          (32 * (((1900178437 / 100000000000000000000) : ℝ) + (1351940593 / 100000000000000000000) + (15436417 / 3125000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12549
