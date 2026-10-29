import BstLean.Part266Shard8Step4


/-! A coarse bound on the actual paper statistics constant at dimension 12550. -/
namespace BstLean.Part266.Row12550
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12548 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12548 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12548 128 ≤ (12802 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12802 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12550) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12550 : ℕ))
    (by norm_num : (12550 : ℕ) ≤ 16384)
  have ht : paperTail256 12550 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12550 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12550 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12550 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12550 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12550 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12548 128 * √(2 / (12550 : ℝ)) *
      (√(12550 : ℝ) + paperT0 12550 + paperTail256 12550) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12550 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12550 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12550 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12548 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12548 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12550 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12550

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12550
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12550 (61 / 100) 162 (17 / (100 * 12550)) (26 / (10 * 12550)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12550 (61 / 100) 162 (17 / (100 * 12550)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (493841811 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1573997827 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1407584133 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12550 / 12550 * (61 / 100)) ^ 4 * inverseRadius8 (12550 - 1) /
            envelopeGap 12550 (61 / 100) 162 (17 / (100 * 12550)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12550

namespace BstLean.Part266.Row12550
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12550 162 ≤ (4720873459 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12550 162 ≤ (1574963453 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (94635767 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12550 162 ≤ (949861867 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12550 162 ≤ (1351617193 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12550 162 ≤ (246923633 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (493841811 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (493841811 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1573997827 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1407584133 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((230029 / 62500000) : ℝ) ≤ √(17 / (100 * 12550) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12550) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1111127593 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4959205183 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12550) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12550) ≤ (5634317 / 50000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12550) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12550 * (162 : ℝ) ^ 2 + 26 / (10 * 12550) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12550) : ℝ)) (tA 12550 * 162 ^ 2 + 26 / (10 * 12550)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((230029 / 62500000))) * ((493841811 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((230029 / 62500000)) ^ 3) * ((1573997827 / 1000000000000000000000000))) + ((1407584133 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((230029 / 62500000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12550) : ℝ)) d.D d.V d.P (√(tA 12550) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((230029 / 62500000)) ^ 2 * (((1111127593 / 500000000000000)) * ((4959205183 / 125000000000000000)))) + ((1407584133 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12550) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((230029 / 62500000)) * ((493841811 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12550) : ℝ)) (tA 12550 * 162 ^ 2 + 26 / (10 * 12550)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((493841811 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((230029 / 62500000)) ^ 2) * ((1573997827 / 1000000000000000000000000)) + ((1407584133 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12550) : ℝ)) (√(26 / (10 * 12550) : ℝ)) d.D d.V d.P (√(tA 12550) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((230029 / 62500000)) * (((1111127593 / 500000000000000)) * ((4959205183 / 125000000000000000))) + ((1407584133 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12550) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((493841811 / 100000000000000000000) : ℝ) + ((1407584133 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12550

namespace BstLean.Part266.Row12550
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12550 162 ∧
    0 ≤ (tableEnvelope C).f1 12550 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12550 162 ∧
    0 ≤ (tableEnvelope C).w1 12550 162 ∧ 0 ≤ (tableEnvelope C).w2 12550 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12550 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12550 162 ∧ 0 ≤ d.f1 12550 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12550 162 ∧ 0 ≤ d.w1 12550 162 ∧ 0 ≤ d.w2 12550 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12550 ≤ 2 * (228 / 100 : ℝ) / 12550 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12550 ≤ 2 * (370 / 100 : ℝ) / 12550 := by
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
    (completeRAData (tableEnvelope C) 12550 162).locationBound 12550 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12550 162).energyBound 12550 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12550 162) (d.f1 12550 162) d.f2 ≤
      32 * (((4720873459 / 1000000000000000000) : ℝ) + (1574963453 / 1000000000000000000) + (94635767 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12550 162) (d.w1 12550 162)
      (d.w2 12550 162) ≤
      32 * (((949861867 / 50000000000000000000) : ℝ) + (1351617193 / 100000000000000000000) + (246923633 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12550 162) (d.f1 12550 162) d.f2 ≤
      ((4720873459 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4720873459 / 1000000000000000000)) * ((1574963453 / 1000000000000000000)) * (126 / 100) +
      2 * (((1574963453 / 1000000000000000000)) ^ 2 + 2 * ((4720873459 / 1000000000000000000)) * ((94635767 / 250000000000000000))) +
      6 * ((1574963453 / 1000000000000000000)) * ((94635767 / 250000000000000000)) * (126 / 100) + 8 * ((94635767 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12550 162) (d.f1 12550 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12550 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12550 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12550 162) (d.f1 12550 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12550 162) (d.w1 12550 162) (d.w2 12550 162)
  have hwexpr0 : 0 ≤ d.w0 12550 162 + d.w1 12550 162 * √(π / 2) +
      2 * d.w2 12550 162 + energyR16 12550 *
      radiusPolynomialRoot16 (d.w0 12550 162) (d.w1 12550 162) (d.w2 12550 162) := by
    positivity
  constructor
  · change (12550 : ℝ) ^ 8 * (mA 12550 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12550 162) (d.f1 12550 162) d.f2 + locationR16 12550 *
        radiusPolynomialRoot16 (d.f0 12550 162) (d.f1 12550 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12550 : ℝ) ^ 8 * (mA 12550 : ℝ) ^ 8 *
        ((((4720873459 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4720873459 / 1000000000000000000)) * ((1574963453 / 1000000000000000000)) * (126 / 100) +
          2 * (((1574963453 / 1000000000000000000)) ^ 2 + 2 * ((4720873459 / 1000000000000000000)) * ((94635767 / 250000000000000000))) +
          6 * ((1574963453 / 1000000000000000000)) * ((94635767 / 250000000000000000)) * (126 / 100) + 8 * ((94635767 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12550) *
          (32 * (((4720873459 / 1000000000000000000) : ℝ) + (1574963453 / 1000000000000000000) + (94635767 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12550 : ℝ) ^ 16 *
      (d.w0 12550 162 + d.w1 12550 162 * √(π / 2) + 2 * d.w2 12550 162 +
        energyR16 12550 * radiusPolynomialRoot16 (d.w0 12550 162) (d.w1 12550 162)
          (d.w2 12550 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12550 : ℝ) ^ 16 *
        (((949861867 / 50000000000000000000) : ℝ) + ((1351617193 / 100000000000000000000)) * (126 / 100) + 2 * ((246923633 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12550) *
          (32 * (((949861867 / 50000000000000000000) : ℝ) + (1351617193 / 100000000000000000000) + (246923633 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12550

/-! A coarse bound on the actual paper statistics constant at dimension 12551. -/
namespace BstLean.Part266.Row12551
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12549 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12549 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12549 128 ≤ (12803 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12803 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12551) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12551 : ℕ))
    (by norm_num : (12551 : ℕ) ≤ 16384)
  have ht : paperTail256 12551 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12551 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12551 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12551 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12551 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12551 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12549 128 * √(2 / (12551 : ℝ)) *
      (√(12551 : ℝ) + paperT0 12551 + paperTail256 12551) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12551 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12551 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12551 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12549 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12549 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12551 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12551

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12551
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12551 (61 / 100) 162 (17 / (100 * 12551)) (26 / (10 * 12551)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12551 (61 / 100) 162 (17 / (100 * 12551)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (246861887 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (786748117 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (281335671 / 50000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12551 / 12551 * (61 / 100)) ^ 4 * inverseRadius8 (12551 - 1) /
            envelopeGap 12551 (61 / 100) 162 (17 / (100 * 12551)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12551

namespace BstLean.Part266.Row12551
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12551 162 ≤ (4719934511 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12551 162 ≤ (1574650061 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (189233853 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12551 162 ≤ (29676093 / 1562500000000000000)
  w1 : (tableEnvelope C).w1 12551 162 ≤ (135129427 / 10000000000000000000)
  w2 : (tableEnvelope C).w2 12551 162 ≤ (19749169 / 4000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (246861887 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (246861887 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (786748117 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (281335671 / 50000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3680317 / 1000000000) : ℝ) ≤ √(17 / (100 * 12551) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12551) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2221989591 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39667319471 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12551) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12551) ≤ (56338681 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12551) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12551 * (162 : ℝ) ^ 2 + 26 / (10 * 12551) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12551) : ℝ)) (tA 12551 * 162 ^ 2 + 26 / (10 * 12551)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3680317 / 1000000000))) * ((246861887 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3680317 / 1000000000)) ^ 3) * ((786748117 / 500000000000000000000000))) + ((281335671 / 50000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3680317 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12551) : ℝ)) d.D d.V d.P (√(tA 12551) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3680317 / 1000000000)) ^ 2 * (((2221989591 / 1000000000000000)) * ((39667319471 / 1000000000000000000)))) + ((281335671 / 50000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12551) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3680317 / 1000000000)) * ((246861887 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12551) : ℝ)) (tA 12551 * 162 ^ 2 + 26 / (10 * 12551)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((246861887 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3680317 / 1000000000)) ^ 2) * ((786748117 / 500000000000000000000000)) + ((281335671 / 50000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12551) : ℝ)) (√(26 / (10 * 12551) : ℝ)) d.D d.V d.P (√(tA 12551) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3680317 / 1000000000)) * (((2221989591 / 1000000000000000)) * ((39667319471 / 1000000000000000000))) + ((281335671 / 50000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12551) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((246861887 / 50000000000000000000) : ℝ) + ((281335671 / 50000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12551

namespace BstLean.Part266.Row12551
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12551 162 ∧
    0 ≤ (tableEnvelope C).f1 12551 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12551 162 ∧
    0 ≤ (tableEnvelope C).w1 12551 162 ∧ 0 ≤ (tableEnvelope C).w2 12551 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12551 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12551 162 ∧ 0 ≤ d.f1 12551 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12551 162 ∧ 0 ≤ d.w1 12551 162 ∧ 0 ≤ d.w2 12551 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12551 ≤ 2 * (228 / 100 : ℝ) / 12551 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12551 ≤ 2 * (370 / 100 : ℝ) / 12551 := by
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
    (completeRAData (tableEnvelope C) 12551 162).locationBound 12551 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12551 162).energyBound 12551 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12551 162) (d.f1 12551 162) d.f2 ≤
      32 * (((4719934511 / 1000000000000000000) : ℝ) + (1574650061 / 1000000000000000000) + (189233853 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12551 162) (d.w1 12551 162)
      (d.w2 12551 162) ≤
      32 * (((29676093 / 1562500000000000000) : ℝ) + (135129427 / 10000000000000000000) + (19749169 / 4000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12551 162) (d.f1 12551 162) d.f2 ≤
      ((4719934511 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4719934511 / 1000000000000000000)) * ((1574650061 / 1000000000000000000)) * (126 / 100) +
      2 * (((1574650061 / 1000000000000000000)) ^ 2 + 2 * ((4719934511 / 1000000000000000000)) * ((189233853 / 500000000000000000))) +
      6 * ((1574650061 / 1000000000000000000)) * ((189233853 / 500000000000000000)) * (126 / 100) + 8 * ((189233853 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12551 162) (d.f1 12551 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12551 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12551 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12551 162) (d.f1 12551 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12551 162) (d.w1 12551 162) (d.w2 12551 162)
  have hwexpr0 : 0 ≤ d.w0 12551 162 + d.w1 12551 162 * √(π / 2) +
      2 * d.w2 12551 162 + energyR16 12551 *
      radiusPolynomialRoot16 (d.w0 12551 162) (d.w1 12551 162) (d.w2 12551 162) := by
    positivity
  constructor
  · change (12551 : ℝ) ^ 8 * (mA 12551 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12551 162) (d.f1 12551 162) d.f2 + locationR16 12551 *
        radiusPolynomialRoot16 (d.f0 12551 162) (d.f1 12551 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12551 : ℝ) ^ 8 * (mA 12551 : ℝ) ^ 8 *
        ((((4719934511 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4719934511 / 1000000000000000000)) * ((1574650061 / 1000000000000000000)) * (126 / 100) +
          2 * (((1574650061 / 1000000000000000000)) ^ 2 + 2 * ((4719934511 / 1000000000000000000)) * ((189233853 / 500000000000000000))) +
          6 * ((1574650061 / 1000000000000000000)) * ((189233853 / 500000000000000000)) * (126 / 100) + 8 * ((189233853 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12551) *
          (32 * (((4719934511 / 1000000000000000000) : ℝ) + (1574650061 / 1000000000000000000) + (189233853 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12551 : ℝ) ^ 16 *
      (d.w0 12551 162 + d.w1 12551 162 * √(π / 2) + 2 * d.w2 12551 162 +
        energyR16 12551 * radiusPolynomialRoot16 (d.w0 12551 162) (d.w1 12551 162)
          (d.w2 12551 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12551 : ℝ) ^ 16 *
        (((29676093 / 1562500000000000000) : ℝ) + ((135129427 / 10000000000000000000)) * (126 / 100) + 2 * ((19749169 / 4000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12551) *
          (32 * (((29676093 / 1562500000000000000) : ℝ) + (135129427 / 10000000000000000000) + (19749169 / 4000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12551

/-! A coarse bound on the actual paper statistics constant at dimension 12552. -/
namespace BstLean.Part266.Row12552
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12550 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12550 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12550 128 ≤ (12804 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12804 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12552) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12552 : ℕ))
    (by norm_num : (12552 : ℕ) ≤ 16384)
  have ht : paperTail256 12552 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12552 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12552 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12552 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12552 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12552 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12550 128 * √(2 / (12552 : ℝ)) *
      (√(12552 : ℝ) + paperT0 12552 + paperTail256 12552) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12552 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12552 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12552 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12550 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12550 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12552 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12552

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12552
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12552 (61 / 100) 162 (17 / (100 * 12552)) (26 / (10 * 12552)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12552 (61 / 100) 162 (17 / (100 * 12552)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (246802887 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1572994841 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2811546467 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12552 / 12552 * (61 / 100)) ^ 4 * inverseRadius8 (12552 - 1) /
            envelopeGap 12552 (61 / 100) 162 (17 / (100 * 12552)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12552

namespace BstLean.Part266.Row12552
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12552 162 ≤ (471899589 / 100000000000000000)
  f1 : (tableEnvelope C).f1 12552 162 ≤ (1574336771 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (189196183 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12552 162 ≤ (237352041 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 12552 162 ≤ (270194291 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12552 162 ≤ (246805611 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (246802887 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (246802887 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1572994841 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2811546467 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((368017 / 100000000) : ℝ) ≤ √(17 / (100 * 12552) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12552) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2221724047 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (2478812437 / 62500000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12552) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12552) ≤ (22533677 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12552) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12552 * (162 : ℝ) ^ 2 + 26 / (10 * 12552) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12552) : ℝ)) (tA 12552 * 162 ^ 2 + 26 / (10 * 12552)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((368017 / 100000000))) * ((246802887 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((368017 / 100000000)) ^ 3) * ((1572994841 / 1000000000000000000000000))) + ((2811546467 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((368017 / 100000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12552) : ℝ)) d.D d.V d.P (√(tA 12552) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((368017 / 100000000)) ^ 2 * (((2221724047 / 1000000000000000)) * ((2478812437 / 62500000000000000)))) + ((2811546467 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12552) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((368017 / 100000000)) * ((246802887 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12552) : ℝ)) (tA 12552 * 162 ^ 2 + 26 / (10 * 12552)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((246802887 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((368017 / 100000000)) ^ 2) * ((1572994841 / 1000000000000000000000000)) + ((2811546467 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12552) : ℝ)) (√(26 / (10 * 12552) : ℝ)) d.D d.V d.P (√(tA 12552) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((368017 / 100000000)) * (((2221724047 / 1000000000000000)) * ((2478812437 / 62500000000000000))) + ((2811546467 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12552) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((246802887 / 50000000000000000000) : ℝ) + ((2811546467 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12552

namespace BstLean.Part266.Row12552
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12552 162 ∧
    0 ≤ (tableEnvelope C).f1 12552 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12552 162 ∧
    0 ≤ (tableEnvelope C).w1 12552 162 ∧ 0 ≤ (tableEnvelope C).w2 12552 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12552 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12552 162 ∧ 0 ≤ d.f1 12552 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12552 162 ∧ 0 ≤ d.w1 12552 162 ∧ 0 ≤ d.w2 12552 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12552 ≤ 2 * (228 / 100 : ℝ) / 12552 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12552 ≤ 2 * (370 / 100 : ℝ) / 12552 := by
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
    (completeRAData (tableEnvelope C) 12552 162).locationBound 12552 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12552 162).energyBound 12552 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12552 162) (d.f1 12552 162) d.f2 ≤
      32 * (((471899589 / 100000000000000000) : ℝ) + (1574336771 / 1000000000000000000) + (189196183 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12552 162) (d.w1 12552 162)
      (d.w2 12552 162) ≤
      32 * (((237352041 / 12500000000000000000) : ℝ) + (270194291 / 20000000000000000000) + (246805611 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12552 162) (d.f1 12552 162) d.f2 ≤
      ((471899589 / 100000000000000000) : ℝ) ^ 2 + 2 * ((471899589 / 100000000000000000)) * ((1574336771 / 1000000000000000000)) * (126 / 100) +
      2 * (((1574336771 / 1000000000000000000)) ^ 2 + 2 * ((471899589 / 100000000000000000)) * ((189196183 / 500000000000000000))) +
      6 * ((1574336771 / 1000000000000000000)) * ((189196183 / 500000000000000000)) * (126 / 100) + 8 * ((189196183 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12552 162) (d.f1 12552 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12552 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12552 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12552 162) (d.f1 12552 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12552 162) (d.w1 12552 162) (d.w2 12552 162)
  have hwexpr0 : 0 ≤ d.w0 12552 162 + d.w1 12552 162 * √(π / 2) +
      2 * d.w2 12552 162 + energyR16 12552 *
      radiusPolynomialRoot16 (d.w0 12552 162) (d.w1 12552 162) (d.w2 12552 162) := by
    positivity
  constructor
  · change (12552 : ℝ) ^ 8 * (mA 12552 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12552 162) (d.f1 12552 162) d.f2 + locationR16 12552 *
        radiusPolynomialRoot16 (d.f0 12552 162) (d.f1 12552 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12552 : ℝ) ^ 8 * (mA 12552 : ℝ) ^ 8 *
        ((((471899589 / 100000000000000000) : ℝ) ^ 2 + 2 * ((471899589 / 100000000000000000)) * ((1574336771 / 1000000000000000000)) * (126 / 100) +
          2 * (((1574336771 / 1000000000000000000)) ^ 2 + 2 * ((471899589 / 100000000000000000)) * ((189196183 / 500000000000000000))) +
          6 * ((1574336771 / 1000000000000000000)) * ((189196183 / 500000000000000000)) * (126 / 100) + 8 * ((189196183 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12552) *
          (32 * (((471899589 / 100000000000000000) : ℝ) + (1574336771 / 1000000000000000000) + (189196183 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12552 : ℝ) ^ 16 *
      (d.w0 12552 162 + d.w1 12552 162 * √(π / 2) + 2 * d.w2 12552 162 +
        energyR16 12552 * radiusPolynomialRoot16 (d.w0 12552 162) (d.w1 12552 162)
          (d.w2 12552 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12552 : ℝ) ^ 16 *
        (((237352041 / 12500000000000000000) : ℝ) + ((270194291 / 20000000000000000000)) * (126 / 100) + 2 * ((246805611 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12552) *
          (32 * (((237352041 / 12500000000000000000) : ℝ) + (270194291 / 20000000000000000000) + (246805611 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12552

/-! A coarse bound on the actual paper statistics constant at dimension 12553. -/
namespace BstLean.Part266.Row12553
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12551 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12551 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12551 128 ≤ (12805 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12805 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12553) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12553 : ℕ))
    (by norm_num : (12553 : ℕ) ≤ 16384)
  have ht : paperTail256 12553 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12553 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12553 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12553 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12553 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12553 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12551 128 * √(2 / (12553 : ℝ)) *
      (√(12553 : ℝ) + paperT0 12553 + paperTail256 12553) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12553 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12553 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12553 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12551 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12551 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12553 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12553

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12553
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12553 (61 / 100) 162 (17 / (100 * 12553)) (26 / (10 * 12553)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12553 (61 / 100) 162 (17 / (100 * 12553)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (123371953 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (98280853 / 62500000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (43902149 / 7812500000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12553 / 12553 * (61 / 100)) ^ 4 * inverseRadius8 (12553 - 1) /
            envelopeGap 12553 (61 / 100) 162 (17 / (100 * 12553)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12553

namespace BstLean.Part266.Row12553
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12553 162 ≤ (943610779 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12553 162 ≤ (196752841 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (378316947 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12553 162 ≤ (1898362099 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12553 162 ≤ (1350648383 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12553 162 ≤ (61686657 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (123371953 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (123371953 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (98280853 / 62500000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (43902149 / 7812500000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((460003 / 125000000) : ℝ) ≤ √(17 / (100 * 12553) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12553) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2221458557 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39654680027 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12553) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12553) ≤ (11265941 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12553) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12553 * (162 : ℝ) ^ 2 + 26 / (10 * 12553) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12553) : ℝ)) (tA 12553 * 162 ^ 2 + 26 / (10 * 12553)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((460003 / 125000000))) * ((123371953 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((460003 / 125000000)) ^ 3) * ((98280853 / 62500000000000000000000))) + ((43902149 / 7812500000000000000000)) * (3 / 2 * (39895 / 100000) / ((460003 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12553) : ℝ)) d.D d.V d.P (√(tA 12553) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((460003 / 125000000)) ^ 2 * (((2221458557 / 1000000000000000)) * ((39654680027 / 1000000000000000000)))) + ((43902149 / 7812500000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12553) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((460003 / 125000000)) * ((123371953 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12553) : ℝ)) (tA 12553 * 162 ^ 2 + 26 / (10 * 12553)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((123371953 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((460003 / 125000000)) ^ 2) * ((98280853 / 62500000000000000000000)) + ((43902149 / 7812500000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12553) : ℝ)) (√(26 / (10 * 12553) : ℝ)) d.D d.V d.P (√(tA 12553) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((460003 / 125000000)) * (((2221458557 / 1000000000000000)) * ((39654680027 / 1000000000000000000))) + ((43902149 / 7812500000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12553) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((123371953 / 25000000000000000000) : ℝ) + ((43902149 / 7812500000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12553

namespace BstLean.Part266.Row12553
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12553 162 ∧
    0 ≤ (tableEnvelope C).f1 12553 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12553 162 ∧
    0 ≤ (tableEnvelope C).w1 12553 162 ∧ 0 ≤ (tableEnvelope C).w2 12553 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12553 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12553 162 ∧ 0 ≤ d.f1 12553 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12553 162 ∧ 0 ≤ d.w1 12553 162 ∧ 0 ≤ d.w2 12553 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12553 ≤ 2 * (228 / 100 : ℝ) / 12553 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12553 ≤ 2 * (370 / 100 : ℝ) / 12553 := by
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
    (completeRAData (tableEnvelope C) 12553 162).locationBound 12553 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12553 162).energyBound 12553 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12553 162) (d.f1 12553 162) d.f2 ≤
      32 * (((943610779 / 200000000000000000) : ℝ) + (196752841 / 125000000000000000) + (378316947 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12553 162) (d.w1 12553 162)
      (d.w2 12553 162) ≤
      32 * (((1898362099 / 100000000000000000000) : ℝ) + (1350648383 / 100000000000000000000) + (61686657 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12553 162) (d.f1 12553 162) d.f2 ≤
      ((943610779 / 200000000000000000) : ℝ) ^ 2 + 2 * ((943610779 / 200000000000000000)) * ((196752841 / 125000000000000000)) * (126 / 100) +
      2 * (((196752841 / 125000000000000000)) ^ 2 + 2 * ((943610779 / 200000000000000000)) * ((378316947 / 1000000000000000000))) +
      6 * ((196752841 / 125000000000000000)) * ((378316947 / 1000000000000000000)) * (126 / 100) + 8 * ((378316947 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12553 162) (d.f1 12553 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12553 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12553 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12553 162) (d.f1 12553 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12553 162) (d.w1 12553 162) (d.w2 12553 162)
  have hwexpr0 : 0 ≤ d.w0 12553 162 + d.w1 12553 162 * √(π / 2) +
      2 * d.w2 12553 162 + energyR16 12553 *
      radiusPolynomialRoot16 (d.w0 12553 162) (d.w1 12553 162) (d.w2 12553 162) := by
    positivity
  constructor
  · change (12553 : ℝ) ^ 8 * (mA 12553 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12553 162) (d.f1 12553 162) d.f2 + locationR16 12553 *
        radiusPolynomialRoot16 (d.f0 12553 162) (d.f1 12553 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12553 : ℝ) ^ 8 * (mA 12553 : ℝ) ^ 8 *
        ((((943610779 / 200000000000000000) : ℝ) ^ 2 + 2 * ((943610779 / 200000000000000000)) * ((196752841 / 125000000000000000)) * (126 / 100) +
          2 * (((196752841 / 125000000000000000)) ^ 2 + 2 * ((943610779 / 200000000000000000)) * ((378316947 / 1000000000000000000))) +
          6 * ((196752841 / 125000000000000000)) * ((378316947 / 1000000000000000000)) * (126 / 100) + 8 * ((378316947 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12553) *
          (32 * (((943610779 / 200000000000000000) : ℝ) + (196752841 / 125000000000000000) + (378316947 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12553 : ℝ) ^ 16 *
      (d.w0 12553 162 + d.w1 12553 162 * √(π / 2) + 2 * d.w2 12553 162 +
        energyR16 12553 * radiusPolynomialRoot16 (d.w0 12553 162) (d.w1 12553 162)
          (d.w2 12553 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12553 : ℝ) ^ 16 *
        (((1898362099 / 100000000000000000000) : ℝ) + ((1350648383 / 100000000000000000000)) * (126 / 100) + 2 * ((61686657 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12553) *
          (32 * (((1898362099 / 100000000000000000000) : ℝ) + (1350648383 / 100000000000000000000) + (61686657 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12553

/-! A coarse bound on the actual paper statistics constant at dimension 12554. -/
namespace BstLean.Part266.Row12554
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12552 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12552 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12552 128 ≤ (12806 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12806 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12554) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12554 : ℕ))
    (by norm_num : (12554 : ℕ) ≤ 16384)
  have ht : paperTail256 12554 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12554 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12554 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12554 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12554 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12554 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12552 128 * √(2 / (12554 : ℝ)) *
      (√(12554 : ℝ) + paperT0 12554 + paperTail256 12554) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12554 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12554 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12554 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12552 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12552 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12554 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12554

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12554
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12554 (61 / 100) 162 (17 / (100 * 12554)) (26 / (10 * 12554)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12554 (61 / 100) 162 (17 / (100 * 12554)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (493369887 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (785996327 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (561585983 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12554 / 12554 * (61 / 100)) ^ 4 * inverseRadius8 (12554 - 1) /
            envelopeGap 12554 (61 / 100) 162 (17 / (100 * 12554)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12554

namespace BstLean.Part266.Row12554
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12554 162 ≤ (4717115927 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12554 162 ≤ (1573709643 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (94560413 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12554 162 ≤ (189790879 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 12554 162 ≤ (1350325787 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12554 162 ≤ (15417979 / 3125000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (493369887 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (493369887 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (785996327 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (561585983 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3679877 / 1000000000) : ℝ) ≤ √(17 / (100 * 12554) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12554) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2221193119 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9912090641 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12554) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12554) ≤ (28162609 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12554) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12554 * (162 : ℝ) ^ 2 + 26 / (10 * 12554) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12554) : ℝ)) (tA 12554 * 162 ^ 2 + 26 / (10 * 12554)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3679877 / 1000000000))) * ((493369887 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3679877 / 1000000000)) ^ 3) * ((785996327 / 500000000000000000000000))) + ((561585983 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3679877 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12554) : ℝ)) d.D d.V d.P (√(tA 12554) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3679877 / 1000000000)) ^ 2 * (((2221193119 / 1000000000000000)) * ((9912090641 / 250000000000000000)))) + ((561585983 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12554) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3679877 / 1000000000)) * ((493369887 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12554) : ℝ)) (tA 12554 * 162 ^ 2 + 26 / (10 * 12554)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((493369887 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3679877 / 1000000000)) ^ 2) * ((785996327 / 500000000000000000000000)) + ((561585983 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12554) : ℝ)) (√(26 / (10 * 12554) : ℝ)) d.D d.V d.P (√(tA 12554) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3679877 / 1000000000)) * (((2221193119 / 1000000000000000)) * ((9912090641 / 250000000000000000))) + ((561585983 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12554) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((493369887 / 100000000000000000000) : ℝ) + ((561585983 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12554

namespace BstLean.Part266.Row12554
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12554 162 ∧
    0 ≤ (tableEnvelope C).f1 12554 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12554 162 ∧
    0 ≤ (tableEnvelope C).w1 12554 162 ∧ 0 ≤ (tableEnvelope C).w2 12554 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12554 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12554 162 ∧ 0 ≤ d.f1 12554 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12554 162 ∧ 0 ≤ d.w1 12554 162 ∧ 0 ≤ d.w2 12554 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12554 ≤ 2 * (228 / 100 : ℝ) / 12554 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12554 ≤ 2 * (370 / 100 : ℝ) / 12554 := by
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
    (completeRAData (tableEnvelope C) 12554 162).locationBound 12554 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12554 162).energyBound 12554 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12554 162) (d.f1 12554 162) d.f2 ≤
      32 * (((4717115927 / 1000000000000000000) : ℝ) + (1573709643 / 1000000000000000000) + (94560413 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12554 162) (d.w1 12554 162)
      (d.w2 12554 162) ≤
      32 * (((189790879 / 10000000000000000000) : ℝ) + (1350325787 / 100000000000000000000) + (15417979 / 3125000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12554 162) (d.f1 12554 162) d.f2 ≤
      ((4717115927 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4717115927 / 1000000000000000000)) * ((1573709643 / 1000000000000000000)) * (126 / 100) +
      2 * (((1573709643 / 1000000000000000000)) ^ 2 + 2 * ((4717115927 / 1000000000000000000)) * ((94560413 / 250000000000000000))) +
      6 * ((1573709643 / 1000000000000000000)) * ((94560413 / 250000000000000000)) * (126 / 100) + 8 * ((94560413 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12554 162) (d.f1 12554 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12554 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12554 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12554 162) (d.f1 12554 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12554 162) (d.w1 12554 162) (d.w2 12554 162)
  have hwexpr0 : 0 ≤ d.w0 12554 162 + d.w1 12554 162 * √(π / 2) +
      2 * d.w2 12554 162 + energyR16 12554 *
      radiusPolynomialRoot16 (d.w0 12554 162) (d.w1 12554 162) (d.w2 12554 162) := by
    positivity
  constructor
  · change (12554 : ℝ) ^ 8 * (mA 12554 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12554 162) (d.f1 12554 162) d.f2 + locationR16 12554 *
        radiusPolynomialRoot16 (d.f0 12554 162) (d.f1 12554 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12554 : ℝ) ^ 8 * (mA 12554 : ℝ) ^ 8 *
        ((((4717115927 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4717115927 / 1000000000000000000)) * ((1573709643 / 1000000000000000000)) * (126 / 100) +
          2 * (((1573709643 / 1000000000000000000)) ^ 2 + 2 * ((4717115927 / 1000000000000000000)) * ((94560413 / 250000000000000000))) +
          6 * ((1573709643 / 1000000000000000000)) * ((94560413 / 250000000000000000)) * (126 / 100) + 8 * ((94560413 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12554) *
          (32 * (((4717115927 / 1000000000000000000) : ℝ) + (1573709643 / 1000000000000000000) + (94560413 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12554 : ℝ) ^ 16 *
      (d.w0 12554 162 + d.w1 12554 162 * √(π / 2) + 2 * d.w2 12554 162 +
        energyR16 12554 * radiusPolynomialRoot16 (d.w0 12554 162) (d.w1 12554 162)
          (d.w2 12554 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12554 : ℝ) ^ 16 *
        (((189790879 / 10000000000000000000) : ℝ) + ((1350325787 / 100000000000000000000)) * (126 / 100) + 2 * ((15417979 / 3125000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12554) *
          (32 * (((189790879 / 10000000000000000000) : ℝ) + (1350325787 / 100000000000000000000) + (15417979 / 3125000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12554

/-! A coarse bound on the actual paper statistics constant at dimension 12555. -/
namespace BstLean.Part266.Row12555
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12553 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12553 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12553 128 ≤ (12807 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12807 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12555) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12555 : ℕ))
    (by norm_num : (12555 : ℕ) ≤ 16384)
  have ht : paperTail256 12555 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12555 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12555 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12555 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12555 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12555 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12553 128 * √(2 / (12555 : ℝ)) *
      (√(12555 : ℝ) + paperT0 12555 + paperTail256 12555) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12555 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12555 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12555 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12553 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12553 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12555 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12555

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12555
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12555 (61 / 100) 162 (17 / (100 * 12555)) (26 / (10 * 12555)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12555 (61 / 100) 162 (17 / (100 * 12555)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (123313 / 25000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (78574593 / 50000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (701530901 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12555 / 12555 * (61 / 100)) ^ 4 * inverseRadius8 (12555 - 1) /
            envelopeGap 12555 (61 / 100) 162 (17 / (100 * 12555)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12555

namespace BstLean.Part266.Row12555
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12555 162 ≤ (2358087293 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12555 162 ≤ (314679161 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (189083139 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12555 162 ≤ (1897454877 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12555 162 ≤ (675001467 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12555 162 ≤ (493257437 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (123313 / 25000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (123313 / 25000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (78574593 / 50000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (701530901 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3679731 / 1000000000) : ℝ) ≤ √(17 / (100 * 12555) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12555) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (444185547 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19821023309 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12555) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12555) ≤ (112641463 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12555) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12555 * (162 : ℝ) ^ 2 + 26 / (10 * 12555) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12555) : ℝ)) (tA 12555 * 162 ^ 2 + 26 / (10 * 12555)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3679731 / 1000000000))) * ((123313 / 25000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3679731 / 1000000000)) ^ 3) * ((78574593 / 50000000000000000000000))) + ((701530901 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3679731 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12555) : ℝ)) d.D d.V d.P (√(tA 12555) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3679731 / 1000000000)) ^ 2 * (((444185547 / 200000000000000)) * ((19821023309 / 500000000000000000)))) + ((701530901 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12555) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3679731 / 1000000000)) * ((123313 / 25000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12555) : ℝ)) (tA 12555 * 162 ^ 2 + 26 / (10 * 12555)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((123313 / 25000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3679731 / 1000000000)) ^ 2) * ((78574593 / 50000000000000000000000)) + ((701530901 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12555) : ℝ)) (√(26 / (10 * 12555) : ℝ)) d.D d.V d.P (√(tA 12555) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3679731 / 1000000000)) * (((444185547 / 200000000000000)) * ((19821023309 / 500000000000000000))) + ((701530901 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12555) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((123313 / 25000000000000000) : ℝ) + ((701530901 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12555

namespace BstLean.Part266.Row12555
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12555 162 ∧
    0 ≤ (tableEnvelope C).f1 12555 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12555 162 ∧
    0 ≤ (tableEnvelope C).w1 12555 162 ∧ 0 ≤ (tableEnvelope C).w2 12555 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12555 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12555 162 ∧ 0 ≤ d.f1 12555 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12555 162 ∧ 0 ≤ d.w1 12555 162 ∧ 0 ≤ d.w2 12555 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12555 ≤ 2 * (228 / 100 : ℝ) / 12555 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12555 ≤ 2 * (370 / 100 : ℝ) / 12555 := by
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
    (completeRAData (tableEnvelope C) 12555 162).locationBound 12555 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12555 162).energyBound 12555 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12555 162) (d.f1 12555 162) d.f2 ≤
      32 * (((2358087293 / 500000000000000000) : ℝ) + (314679161 / 200000000000000000) + (189083139 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12555 162) (d.w1 12555 162)
      (d.w2 12555 162) ≤
      32 * (((1897454877 / 100000000000000000000) : ℝ) + (675001467 / 50000000000000000000) + (493257437 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12555 162) (d.f1 12555 162) d.f2 ≤
      ((2358087293 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2358087293 / 500000000000000000)) * ((314679161 / 200000000000000000)) * (126 / 100) +
      2 * (((314679161 / 200000000000000000)) ^ 2 + 2 * ((2358087293 / 500000000000000000)) * ((189083139 / 500000000000000000))) +
      6 * ((314679161 / 200000000000000000)) * ((189083139 / 500000000000000000)) * (126 / 100) + 8 * ((189083139 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12555 162) (d.f1 12555 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12555 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12555 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12555 162) (d.f1 12555 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12555 162) (d.w1 12555 162) (d.w2 12555 162)
  have hwexpr0 : 0 ≤ d.w0 12555 162 + d.w1 12555 162 * √(π / 2) +
      2 * d.w2 12555 162 + energyR16 12555 *
      radiusPolynomialRoot16 (d.w0 12555 162) (d.w1 12555 162) (d.w2 12555 162) := by
    positivity
  constructor
  · change (12555 : ℝ) ^ 8 * (mA 12555 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12555 162) (d.f1 12555 162) d.f2 + locationR16 12555 *
        radiusPolynomialRoot16 (d.f0 12555 162) (d.f1 12555 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12555 : ℝ) ^ 8 * (mA 12555 : ℝ) ^ 8 *
        ((((2358087293 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2358087293 / 500000000000000000)) * ((314679161 / 200000000000000000)) * (126 / 100) +
          2 * (((314679161 / 200000000000000000)) ^ 2 + 2 * ((2358087293 / 500000000000000000)) * ((189083139 / 500000000000000000))) +
          6 * ((314679161 / 200000000000000000)) * ((189083139 / 500000000000000000)) * (126 / 100) + 8 * ((189083139 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12555) *
          (32 * (((2358087293 / 500000000000000000) : ℝ) + (314679161 / 200000000000000000) + (189083139 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12555 : ℝ) ^ 16 *
      (d.w0 12555 162 + d.w1 12555 162 * √(π / 2) + 2 * d.w2 12555 162 +
        energyR16 12555 * radiusPolynomialRoot16 (d.w0 12555 162) (d.w1 12555 162)
          (d.w2 12555 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12555 : ℝ) ^ 16 *
        (((1897454877 / 100000000000000000000) : ℝ) + ((675001467 / 50000000000000000000)) * (126 / 100) + 2 * ((493257437 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12555) *
          (32 * (((1897454877 / 100000000000000000000) : ℝ) + (675001467 / 50000000000000000000) + (493257437 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12555

/-! A coarse bound on the actual paper statistics constant at dimension 12556. -/
namespace BstLean.Part266.Row12556
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12554 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12554 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12554 128 ≤ (12808 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12808 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12556) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12556 : ℕ))
    (by norm_num : (12556 : ℕ) ≤ 16384)
  have ht : paperTail256 12556 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12556 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12556 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12556 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12556 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12556 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12554 128 * √(2 / (12556 : ℝ)) *
      (√(12556 : ℝ) + paperT0 12556 + paperTail256 12556) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12556 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12556 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12556 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12554 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12554 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12556 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12556

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12556
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12556 (61 / 100) 162 (17 / (100 * 12556)) (26 / (10 * 12556)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12556 (61 / 100) 162 (17 / (100 * 12556)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (493134151 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (785495633 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5608637203 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12556 / 12556 * (61 / 100)) ^ 4 * inverseRadius8 (12556 - 1) /
            envelopeGap 12556 (61 / 100) 162 (17 / (100 * 12556)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12556

namespace BstLean.Part266.Row12556
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12556 162 ≤ (2357618637 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12556 162 ≤ (786541463 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (37809103 / 100000000000000000)
  w0 : (tableEnvelope C).w0 12556 162 ≤ (379400377 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12556 162 ≤ (1349680557 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12556 162 ≤ (98627917 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (493134151 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (493134151 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (785495633 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5608637203 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((114987 / 31250000) : ℝ) ≤ √(17 / (100 * 12556) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12556) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (555165601 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9908933047 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12556) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12556) ≤ (28158123 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12556) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12556 * (162 : ℝ) ^ 2 + 26 / (10 * 12556) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12556) : ℝ)) (tA 12556 * 162 ^ 2 + 26 / (10 * 12556)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((114987 / 31250000))) * ((493134151 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((114987 / 31250000)) ^ 3) * ((785495633 / 500000000000000000000000))) + ((5608637203 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((114987 / 31250000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12556) : ℝ)) d.D d.V d.P (√(tA 12556) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((114987 / 31250000)) ^ 2 * (((555165601 / 250000000000000)) * ((9908933047 / 250000000000000000)))) + ((5608637203 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12556) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((114987 / 31250000)) * ((493134151 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12556) : ℝ)) (tA 12556 * 162 ^ 2 + 26 / (10 * 12556)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((493134151 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((114987 / 31250000)) ^ 2) * ((785495633 / 500000000000000000000000)) + ((5608637203 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12556) : ℝ)) (√(26 / (10 * 12556) : ℝ)) d.D d.V d.P (√(tA 12556) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((114987 / 31250000)) * (((555165601 / 250000000000000)) * ((9908933047 / 250000000000000000))) + ((5608637203 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12556) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((493134151 / 100000000000000000000) : ℝ) + ((5608637203 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12556

namespace BstLean.Part266.Row12556
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12556 162 ∧
    0 ≤ (tableEnvelope C).f1 12556 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12556 162 ∧
    0 ≤ (tableEnvelope C).w1 12556 162 ∧ 0 ≤ (tableEnvelope C).w2 12556 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12556 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12556 162 ∧ 0 ≤ d.f1 12556 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12556 162 ∧ 0 ≤ d.w1 12556 162 ∧ 0 ≤ d.w2 12556 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12556 ≤ 2 * (228 / 100 : ℝ) / 12556 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12556 ≤ 2 * (370 / 100 : ℝ) / 12556 := by
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
    (completeRAData (tableEnvelope C) 12556 162).locationBound 12556 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12556 162).energyBound 12556 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12556 162) (d.f1 12556 162) d.f2 ≤
      32 * (((2357618637 / 500000000000000000) : ℝ) + (786541463 / 500000000000000000) + (37809103 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12556 162) (d.w1 12556 162)
      (d.w2 12556 162) ≤
      32 * (((379400377 / 20000000000000000000) : ℝ) + (1349680557 / 100000000000000000000) + (98627917 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12556 162) (d.f1 12556 162) d.f2 ≤
      ((2357618637 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2357618637 / 500000000000000000)) * ((786541463 / 500000000000000000)) * (126 / 100) +
      2 * (((786541463 / 500000000000000000)) ^ 2 + 2 * ((2357618637 / 500000000000000000)) * ((37809103 / 100000000000000000))) +
      6 * ((786541463 / 500000000000000000)) * ((37809103 / 100000000000000000)) * (126 / 100) + 8 * ((37809103 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12556 162) (d.f1 12556 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12556 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12556 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12556 162) (d.f1 12556 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12556 162) (d.w1 12556 162) (d.w2 12556 162)
  have hwexpr0 : 0 ≤ d.w0 12556 162 + d.w1 12556 162 * √(π / 2) +
      2 * d.w2 12556 162 + energyR16 12556 *
      radiusPolynomialRoot16 (d.w0 12556 162) (d.w1 12556 162) (d.w2 12556 162) := by
    positivity
  constructor
  · change (12556 : ℝ) ^ 8 * (mA 12556 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12556 162) (d.f1 12556 162) d.f2 + locationR16 12556 *
        radiusPolynomialRoot16 (d.f0 12556 162) (d.f1 12556 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12556 : ℝ) ^ 8 * (mA 12556 : ℝ) ^ 8 *
        ((((2357618637 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2357618637 / 500000000000000000)) * ((786541463 / 500000000000000000)) * (126 / 100) +
          2 * (((786541463 / 500000000000000000)) ^ 2 + 2 * ((2357618637 / 500000000000000000)) * ((37809103 / 100000000000000000))) +
          6 * ((786541463 / 500000000000000000)) * ((37809103 / 100000000000000000)) * (126 / 100) + 8 * ((37809103 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12556) *
          (32 * (((2357618637 / 500000000000000000) : ℝ) + (786541463 / 500000000000000000) + (37809103 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12556 : ℝ) ^ 16 *
      (d.w0 12556 162 + d.w1 12556 162 * √(π / 2) + 2 * d.w2 12556 162 +
        energyR16 12556 * radiusPolynomialRoot16 (d.w0 12556 162) (d.w1 12556 162)
          (d.w2 12556 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12556 : ℝ) ^ 16 *
        (((379400377 / 20000000000000000000) : ℝ) + ((1349680557 / 100000000000000000000)) * (126 / 100) + 2 * ((98627917 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12556) *
          (32 * (((379400377 / 20000000000000000000) : ℝ) + (1349680557 / 100000000000000000000) + (98627917 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12556

/-! A coarse bound on the actual paper statistics constant at dimension 12557. -/
namespace BstLean.Part266.Row12557
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12555 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12555 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12555 128 ≤ (12809 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12809 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12557) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12557 : ℕ))
    (by norm_num : (12557 : ℕ) ≤ 16384)
  have ht : paperTail256 12557 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12557 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12557 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12557 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12557 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12557 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12555 128 * √(2 / (12557 : ℝ)) *
      (√(12557 : ℝ) + paperT0 12557 + paperTail256 12557) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12557 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12557 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12557 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12555 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12555 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12557 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12557

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12557
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12557 (61 / 100) 162 (17 / (100 * 12557)) (26 / (10 * 12557)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12557 (61 / 100) 162 (17 / (100 * 12557)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (493016339 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (157049087 / 100000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1401257453 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12557 / 12557 * (61 / 100)) ^ 4 * inverseRadius8 (12557 - 1) /
            envelopeGap 12557 (61 / 100) 162 (17 / (100 * 12557)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12557

namespace BstLean.Part266.Row12557
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12557 162 ≤ (942859317 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12557 162 ≤ (393192323 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (378015701 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12557 162 ≤ (1896548287 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12557 162 ≤ (674678961 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12557 162 ≤ (493021769 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (493016339 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (493016339 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (157049087 / 100000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1401257453 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1839719 / 500000000) : ℝ) ≤ √(17 / (100 * 12557) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12557) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (17763177 / 8000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39629419249 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12557) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12557) ≤ (56311761 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12557) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12557 * (162 : ℝ) ^ 2 + 26 / (10 * 12557) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12557) : ℝ)) (tA 12557 * 162 ^ 2 + 26 / (10 * 12557)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1839719 / 500000000))) * ((493016339 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1839719 / 500000000)) ^ 3) * ((157049087 / 100000000000000000000000))) + ((1401257453 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1839719 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12557) : ℝ)) d.D d.V d.P (√(tA 12557) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1839719 / 500000000)) ^ 2 * (((17763177 / 8000000000000)) * ((39629419249 / 1000000000000000000)))) + ((1401257453 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12557) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1839719 / 500000000)) * ((493016339 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12557) : ℝ)) (tA 12557 * 162 ^ 2 + 26 / (10 * 12557)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((493016339 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1839719 / 500000000)) ^ 2) * ((157049087 / 100000000000000000000000)) + ((1401257453 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12557) : ℝ)) (√(26 / (10 * 12557) : ℝ)) d.D d.V d.P (√(tA 12557) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1839719 / 500000000)) * (((17763177 / 8000000000000)) * ((39629419249 / 1000000000000000000))) + ((1401257453 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12557) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((493016339 / 100000000000000000000) : ℝ) + ((1401257453 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12557

namespace BstLean.Part266.Row12557
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12557 162 ∧
    0 ≤ (tableEnvelope C).f1 12557 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12557 162 ∧
    0 ≤ (tableEnvelope C).w1 12557 162 ∧ 0 ≤ (tableEnvelope C).w2 12557 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12557 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12557 162 ∧ 0 ≤ d.f1 12557 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12557 162 ∧ 0 ≤ d.w1 12557 162 ∧ 0 ≤ d.w2 12557 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12557 ≤ 2 * (228 / 100 : ℝ) / 12557 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12557 ≤ 2 * (370 / 100 : ℝ) / 12557 := by
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
    (completeRAData (tableEnvelope C) 12557 162).locationBound 12557 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12557 162).energyBound 12557 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12557 162) (d.f1 12557 162) d.f2 ≤
      32 * (((942859317 / 200000000000000000) : ℝ) + (393192323 / 250000000000000000) + (378015701 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12557 162) (d.w1 12557 162)
      (d.w2 12557 162) ≤
      32 * (((1896548287 / 100000000000000000000) : ℝ) + (674678961 / 50000000000000000000) + (493021769 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12557 162) (d.f1 12557 162) d.f2 ≤
      ((942859317 / 200000000000000000) : ℝ) ^ 2 + 2 * ((942859317 / 200000000000000000)) * ((393192323 / 250000000000000000)) * (126 / 100) +
      2 * (((393192323 / 250000000000000000)) ^ 2 + 2 * ((942859317 / 200000000000000000)) * ((378015701 / 1000000000000000000))) +
      6 * ((393192323 / 250000000000000000)) * ((378015701 / 1000000000000000000)) * (126 / 100) + 8 * ((378015701 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12557 162) (d.f1 12557 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12557 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12557 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12557 162) (d.f1 12557 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12557 162) (d.w1 12557 162) (d.w2 12557 162)
  have hwexpr0 : 0 ≤ d.w0 12557 162 + d.w1 12557 162 * √(π / 2) +
      2 * d.w2 12557 162 + energyR16 12557 *
      radiusPolynomialRoot16 (d.w0 12557 162) (d.w1 12557 162) (d.w2 12557 162) := by
    positivity
  constructor
  · change (12557 : ℝ) ^ 8 * (mA 12557 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12557 162) (d.f1 12557 162) d.f2 + locationR16 12557 *
        radiusPolynomialRoot16 (d.f0 12557 162) (d.f1 12557 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12557 : ℝ) ^ 8 * (mA 12557 : ℝ) ^ 8 *
        ((((942859317 / 200000000000000000) : ℝ) ^ 2 + 2 * ((942859317 / 200000000000000000)) * ((393192323 / 250000000000000000)) * (126 / 100) +
          2 * (((393192323 / 250000000000000000)) ^ 2 + 2 * ((942859317 / 200000000000000000)) * ((378015701 / 1000000000000000000))) +
          6 * ((393192323 / 250000000000000000)) * ((378015701 / 1000000000000000000)) * (126 / 100) + 8 * ((378015701 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12557) *
          (32 * (((942859317 / 200000000000000000) : ℝ) + (393192323 / 250000000000000000) + (378015701 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12557 : ℝ) ^ 16 *
      (d.w0 12557 162 + d.w1 12557 162 * √(π / 2) + 2 * d.w2 12557 162 +
        energyR16 12557 * radiusPolynomialRoot16 (d.w0 12557 162) (d.w1 12557 162)
          (d.w2 12557 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12557 : ℝ) ^ 16 *
        (((1896548287 / 100000000000000000000) : ℝ) + ((674678961 / 50000000000000000000)) * (126 / 100) + 2 * ((493021769 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12557) *
          (32 * (((1896548287 / 100000000000000000000) : ℝ) + (674678961 / 50000000000000000000) + (493021769 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12557

/-! A coarse bound on the actual paper statistics constant at dimension 12558. -/
namespace BstLean.Part266.Row12558
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12556 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12556 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12556 128 ≤ (12810 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12810 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12558) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12558 : ℕ))
    (by norm_num : (12558 : ℕ) ≤ 16384)
  have ht : paperTail256 12558 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12558 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12558 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12558 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12558 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12558 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12556 128 * √(2 / (12558 : ℝ)) *
      (√(12558 : ℝ) + paperT0 12558 + paperTail256 12558) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12558 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12558 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12558 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12556 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12556 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12558 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12558

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12558
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12558 (61 / 100) 162 (17 / (100 * 12558)) (26 / (10 * 12558)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12558 (61 / 100) 162 (17 / (100 * 12558)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (98579713 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (784995337 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2800712517 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12558 / 12558 * (61 / 100)) ^ 4 * inverseRadius8 (12558 - 1) /
            envelopeGap 12558 (61 / 100) 162 (17 / (100 * 12558)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12558

namespace BstLean.Part266.Row12558
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12558 162 ≤ (4713359923 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12558 162 ≤ (1572456617 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (188970249 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12558 162 ≤ (1896095611 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12558 162 ≤ (337258941 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12558 162 ≤ (61612999 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (98579713 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (98579713 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (784995337 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2800712517 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3679291 / 1000000000) : ℝ) ≤ √(17 / (100 * 12558) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12558) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (22201319 / 10000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39623107829 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12558) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12558) ≤ (56307277 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12558) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12558 * (162 : ℝ) ^ 2 + 26 / (10 * 12558) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12558) : ℝ)) (tA 12558 * 162 ^ 2 + 26 / (10 * 12558)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3679291 / 1000000000))) * ((98579713 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3679291 / 1000000000)) ^ 3) * ((784995337 / 500000000000000000000000))) + ((2800712517 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3679291 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12558) : ℝ)) d.D d.V d.P (√(tA 12558) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3679291 / 1000000000)) ^ 2 * (((22201319 / 10000000000000)) * ((39623107829 / 1000000000000000000)))) + ((2800712517 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12558) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3679291 / 1000000000)) * ((98579713 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12558) : ℝ)) (tA 12558 * 162 ^ 2 + 26 / (10 * 12558)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((98579713 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3679291 / 1000000000)) ^ 2) * ((784995337 / 500000000000000000000000)) + ((2800712517 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12558) : ℝ)) (√(26 / (10 * 12558) : ℝ)) d.D d.V d.P (√(tA 12558) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3679291 / 1000000000)) * (((22201319 / 10000000000000)) * ((39623107829 / 1000000000000000000))) + ((2800712517 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12558) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((98579713 / 20000000000000000000) : ℝ) + ((2800712517 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12558

namespace BstLean.Part266.Row12558
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12558 162 ∧
    0 ≤ (tableEnvelope C).f1 12558 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12558 162 ∧
    0 ≤ (tableEnvelope C).w1 12558 162 ∧ 0 ≤ (tableEnvelope C).w2 12558 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12558 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12558 162 ∧ 0 ≤ d.f1 12558 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12558 162 ∧ 0 ≤ d.w1 12558 162 ∧ 0 ≤ d.w2 12558 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12558 ≤ 2 * (228 / 100 : ℝ) / 12558 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12558 ≤ 2 * (370 / 100 : ℝ) / 12558 := by
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
    (completeRAData (tableEnvelope C) 12558 162).locationBound 12558 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12558 162).energyBound 12558 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12558 162) (d.f1 12558 162) d.f2 ≤
      32 * (((4713359923 / 1000000000000000000) : ℝ) + (1572456617 / 1000000000000000000) + (188970249 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12558 162) (d.w1 12558 162)
      (d.w2 12558 162) ≤
      32 * (((1896095611 / 100000000000000000000) : ℝ) + (337258941 / 25000000000000000000) + (61612999 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12558 162) (d.f1 12558 162) d.f2 ≤
      ((4713359923 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4713359923 / 1000000000000000000)) * ((1572456617 / 1000000000000000000)) * (126 / 100) +
      2 * (((1572456617 / 1000000000000000000)) ^ 2 + 2 * ((4713359923 / 1000000000000000000)) * ((188970249 / 500000000000000000))) +
      6 * ((1572456617 / 1000000000000000000)) * ((188970249 / 500000000000000000)) * (126 / 100) + 8 * ((188970249 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12558 162) (d.f1 12558 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12558 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12558 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12558 162) (d.f1 12558 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12558 162) (d.w1 12558 162) (d.w2 12558 162)
  have hwexpr0 : 0 ≤ d.w0 12558 162 + d.w1 12558 162 * √(π / 2) +
      2 * d.w2 12558 162 + energyR16 12558 *
      radiusPolynomialRoot16 (d.w0 12558 162) (d.w1 12558 162) (d.w2 12558 162) := by
    positivity
  constructor
  · change (12558 : ℝ) ^ 8 * (mA 12558 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12558 162) (d.f1 12558 162) d.f2 + locationR16 12558 *
        radiusPolynomialRoot16 (d.f0 12558 162) (d.f1 12558 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12558 : ℝ) ^ 8 * (mA 12558 : ℝ) ^ 8 *
        ((((4713359923 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4713359923 / 1000000000000000000)) * ((1572456617 / 1000000000000000000)) * (126 / 100) +
          2 * (((1572456617 / 1000000000000000000)) ^ 2 + 2 * ((4713359923 / 1000000000000000000)) * ((188970249 / 500000000000000000))) +
          6 * ((1572456617 / 1000000000000000000)) * ((188970249 / 500000000000000000)) * (126 / 100) + 8 * ((188970249 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12558) *
          (32 * (((4713359923 / 1000000000000000000) : ℝ) + (1572456617 / 1000000000000000000) + (188970249 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12558 : ℝ) ^ 16 *
      (d.w0 12558 162 + d.w1 12558 162 * √(π / 2) + 2 * d.w2 12558 162 +
        energyR16 12558 * radiusPolynomialRoot16 (d.w0 12558 162) (d.w1 12558 162)
          (d.w2 12558 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12558 : ℝ) ^ 16 *
        (((1896095611 / 100000000000000000000) : ℝ) + ((337258941 / 25000000000000000000)) * (126 / 100) + 2 * ((61612999 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12558) *
          (32 * (((1896095611 / 100000000000000000000) : ℝ) + (337258941 / 25000000000000000000) + (61612999 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12558

/-! A coarse bound on the actual paper statistics constant at dimension 12559. -/
namespace BstLean.Part266.Row12559
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12557 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12557 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12557 128 ≤ (12811 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12811 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12559) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12559 : ℕ))
    (by norm_num : (12559 : ℕ) ≤ 16384)
  have ht : paperTail256 12559 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12559 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12559 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12559 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12559 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12559 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12557 128 * √(2 / (12559 : ℝ)) *
      (√(12559 : ℝ) + paperT0 12559 + paperTail256 12559) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12559 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12559 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12559 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12557 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12557 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12559 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12559

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12559
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12559 (61 / 100) 162 (17 / (100 * 12559)) (26 / (10 * 12559)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12559 (61 / 100) 162 (17 / (100 * 12559)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (123195207 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1569490677 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5597822867 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12559 / 12559 * (61 / 100)) ^ 4 * inverseRadius8 (12559 - 1) /
            envelopeGap 12559 (61 / 100) 162 (17 / (100 * 12559)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12559

namespace BstLean.Part266.Row12559
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12559 162 ≤ (4712419889 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12559 162 ≤ (393035797 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (75573043 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12559 162 ≤ (236955291 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 12559 162 ≤ (1348713347 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12559 162 ≤ (492786251 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (123195207 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (123195207 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1569490677 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5597822867 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((735829 / 200000000) : ℝ) ≤ √(17 / (100 * 12559) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12559) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1109933363 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7923359583 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12559) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12559) ≤ (112605587 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12559) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12559 * (162 : ℝ) ^ 2 + 26 / (10 * 12559) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12559) : ℝ)) (tA 12559 * 162 ^ 2 + 26 / (10 * 12559)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((735829 / 200000000))) * ((123195207 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((735829 / 200000000)) ^ 3) * ((1569490677 / 1000000000000000000000000))) + ((5597822867 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((735829 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12559) : ℝ)) d.D d.V d.P (√(tA 12559) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((735829 / 200000000)) ^ 2 * (((1109933363 / 500000000000000)) * ((7923359583 / 200000000000000000)))) + ((5597822867 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12559) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((735829 / 200000000)) * ((123195207 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12559) : ℝ)) (tA 12559 * 162 ^ 2 + 26 / (10 * 12559)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((123195207 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((735829 / 200000000)) ^ 2) * ((1569490677 / 1000000000000000000000000)) + ((5597822867 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12559) : ℝ)) (√(26 / (10 * 12559) : ℝ)) d.D d.V d.P (√(tA 12559) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((735829 / 200000000)) * (((1109933363 / 500000000000000)) * ((7923359583 / 200000000000000000))) + ((5597822867 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12559) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((123195207 / 25000000000000000000) : ℝ) + ((5597822867 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12559

namespace BstLean.Part266.Row12559
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12559 162 ∧
    0 ≤ (tableEnvelope C).f1 12559 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12559 162 ∧
    0 ≤ (tableEnvelope C).w1 12559 162 ∧ 0 ≤ (tableEnvelope C).w2 12559 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12559 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12559 162 ∧ 0 ≤ d.f1 12559 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12559 162 ∧ 0 ≤ d.w1 12559 162 ∧ 0 ≤ d.w2 12559 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12559 ≤ 2 * (228 / 100 : ℝ) / 12559 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12559 ≤ 2 * (370 / 100 : ℝ) / 12559 := by
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
    (completeRAData (tableEnvelope C) 12559 162).locationBound 12559 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12559 162).energyBound 12559 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12559 162) (d.f1 12559 162) d.f2 ≤
      32 * (((4712419889 / 1000000000000000000) : ℝ) + (393035797 / 250000000000000000) + (75573043 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12559 162) (d.w1 12559 162)
      (d.w2 12559 162) ≤
      32 * (((236955291 / 12500000000000000000) : ℝ) + (1348713347 / 100000000000000000000) + (492786251 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12559 162) (d.f1 12559 162) d.f2 ≤
      ((4712419889 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4712419889 / 1000000000000000000)) * ((393035797 / 250000000000000000)) * (126 / 100) +
      2 * (((393035797 / 250000000000000000)) ^ 2 + 2 * ((4712419889 / 1000000000000000000)) * ((75573043 / 200000000000000000))) +
      6 * ((393035797 / 250000000000000000)) * ((75573043 / 200000000000000000)) * (126 / 100) + 8 * ((75573043 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12559 162) (d.f1 12559 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12559 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12559 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12559 162) (d.f1 12559 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12559 162) (d.w1 12559 162) (d.w2 12559 162)
  have hwexpr0 : 0 ≤ d.w0 12559 162 + d.w1 12559 162 * √(π / 2) +
      2 * d.w2 12559 162 + energyR16 12559 *
      radiusPolynomialRoot16 (d.w0 12559 162) (d.w1 12559 162) (d.w2 12559 162) := by
    positivity
  constructor
  · change (12559 : ℝ) ^ 8 * (mA 12559 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12559 162) (d.f1 12559 162) d.f2 + locationR16 12559 *
        radiusPolynomialRoot16 (d.f0 12559 162) (d.f1 12559 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12559 : ℝ) ^ 8 * (mA 12559 : ℝ) ^ 8 *
        ((((4712419889 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4712419889 / 1000000000000000000)) * ((393035797 / 250000000000000000)) * (126 / 100) +
          2 * (((393035797 / 250000000000000000)) ^ 2 + 2 * ((4712419889 / 1000000000000000000)) * ((75573043 / 200000000000000000))) +
          6 * ((393035797 / 250000000000000000)) * ((75573043 / 200000000000000000)) * (126 / 100) + 8 * ((75573043 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12559) *
          (32 * (((4712419889 / 1000000000000000000) : ℝ) + (393035797 / 250000000000000000) + (75573043 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12559 : ℝ) ^ 16 *
      (d.w0 12559 162 + d.w1 12559 162 * √(π / 2) + 2 * d.w2 12559 162 +
        energyR16 12559 * radiusPolynomialRoot16 (d.w0 12559 162) (d.w1 12559 162)
          (d.w2 12559 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12559 : ℝ) ^ 16 *
        (((236955291 / 12500000000000000000) : ℝ) + ((1348713347 / 100000000000000000000)) * (126 / 100) + 2 * ((492786251 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12559) *
          (32 * (((236955291 / 12500000000000000000) : ℝ) + (1348713347 / 100000000000000000000) + (492786251 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12559

/-! A coarse bound on the actual paper statistics constant at dimension 12560. -/
namespace BstLean.Part266.Row12560
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12558 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12558 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12558 128 ≤ (12812 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12812 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12560) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12560 : ℕ))
    (by norm_num : (12560 : ℕ) ≤ 16384)
  have ht : paperTail256 12560 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12560 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12560 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12560 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12560 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12560 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12558 128 * √(2 / (12560 : ℝ)) *
      (√(12560 : ℝ) + paperT0 12560 + paperTail256 12560) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12560 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12560 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12560 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12558 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12558 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12560 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12560

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12560
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12560 (61 / 100) 162 (17 / (100 * 12560)) (26 / (10 * 12560)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12560 (61 / 100) 162 (17 / (100 * 12560)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (492663129 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1568990879 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5594223309 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12560 / 12560 * (61 / 100)) ^ 4 * inverseRadius8 (12560 - 1) /
            envelopeGap 12560 (61 / 100) 162 (17 / (100 * 12560)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12560

namespace BstLean.Part266.Row12560
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12560 162 ≤ (4711483879 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12560 162 ≤ (785915359 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (188895029 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12560 162 ≤ (1895189967 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12560 162 ≤ (1348391407 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12560 162 ≤ (492668549 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (492663129 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (492663129 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1568990879 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5594223309 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1839499 / 500000000) : ℝ) ≤ √(17 / (100 * 12560) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12560) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2219601607 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9902622377 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12560) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12560) ≤ (56298311 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12560) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12560 * (162 : ℝ) ^ 2 + 26 / (10 * 12560) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12560) : ℝ)) (tA 12560 * 162 ^ 2 + 26 / (10 * 12560)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1839499 / 500000000))) * ((492663129 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1839499 / 500000000)) ^ 3) * ((1568990879 / 1000000000000000000000000))) + ((5594223309 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1839499 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12560) : ℝ)) d.D d.V d.P (√(tA 12560) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1839499 / 500000000)) ^ 2 * (((2219601607 / 1000000000000000)) * ((9902622377 / 250000000000000000)))) + ((5594223309 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12560) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1839499 / 500000000)) * ((492663129 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12560) : ℝ)) (tA 12560 * 162 ^ 2 + 26 / (10 * 12560)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((492663129 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1839499 / 500000000)) ^ 2) * ((1568990879 / 1000000000000000000000000)) + ((5594223309 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12560) : ℝ)) (√(26 / (10 * 12560) : ℝ)) d.D d.V d.P (√(tA 12560) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1839499 / 500000000)) * (((2219601607 / 1000000000000000)) * ((9902622377 / 250000000000000000))) + ((5594223309 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12560) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((492663129 / 100000000000000000000) : ℝ) + ((5594223309 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12560

namespace BstLean.Part266.Row12560
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12560 162 ∧
    0 ≤ (tableEnvelope C).f1 12560 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12560 162 ∧
    0 ≤ (tableEnvelope C).w1 12560 162 ∧ 0 ≤ (tableEnvelope C).w2 12560 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12560 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12560 162 ∧ 0 ≤ d.f1 12560 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12560 162 ∧ 0 ≤ d.w1 12560 162 ∧ 0 ≤ d.w2 12560 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12560 ≤ 2 * (228 / 100 : ℝ) / 12560 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12560 ≤ 2 * (370 / 100 : ℝ) / 12560 := by
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
    (completeRAData (tableEnvelope C) 12560 162).locationBound 12560 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12560 162).energyBound 12560 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12560 162) (d.f1 12560 162) d.f2 ≤
      32 * (((4711483879 / 1000000000000000000) : ℝ) + (785915359 / 500000000000000000) + (188895029 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12560 162) (d.w1 12560 162)
      (d.w2 12560 162) ≤
      32 * (((1895189967 / 100000000000000000000) : ℝ) + (1348391407 / 100000000000000000000) + (492668549 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12560 162) (d.f1 12560 162) d.f2 ≤
      ((4711483879 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4711483879 / 1000000000000000000)) * ((785915359 / 500000000000000000)) * (126 / 100) +
      2 * (((785915359 / 500000000000000000)) ^ 2 + 2 * ((4711483879 / 1000000000000000000)) * ((188895029 / 500000000000000000))) +
      6 * ((785915359 / 500000000000000000)) * ((188895029 / 500000000000000000)) * (126 / 100) + 8 * ((188895029 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12560 162) (d.f1 12560 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12560 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12560 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12560 162) (d.f1 12560 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12560 162) (d.w1 12560 162) (d.w2 12560 162)
  have hwexpr0 : 0 ≤ d.w0 12560 162 + d.w1 12560 162 * √(π / 2) +
      2 * d.w2 12560 162 + energyR16 12560 *
      radiusPolynomialRoot16 (d.w0 12560 162) (d.w1 12560 162) (d.w2 12560 162) := by
    positivity
  constructor
  · change (12560 : ℝ) ^ 8 * (mA 12560 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12560 162) (d.f1 12560 162) d.f2 + locationR16 12560 *
        radiusPolynomialRoot16 (d.f0 12560 162) (d.f1 12560 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12560 : ℝ) ^ 8 * (mA 12560 : ℝ) ^ 8 *
        ((((4711483879 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4711483879 / 1000000000000000000)) * ((785915359 / 500000000000000000)) * (126 / 100) +
          2 * (((785915359 / 500000000000000000)) ^ 2 + 2 * ((4711483879 / 1000000000000000000)) * ((188895029 / 500000000000000000))) +
          6 * ((785915359 / 500000000000000000)) * ((188895029 / 500000000000000000)) * (126 / 100) + 8 * ((188895029 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12560) *
          (32 * (((4711483879 / 1000000000000000000) : ℝ) + (785915359 / 500000000000000000) + (188895029 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12560 : ℝ) ^ 16 *
      (d.w0 12560 162 + d.w1 12560 162 * √(π / 2) + 2 * d.w2 12560 162 +
        energyR16 12560 * radiusPolynomialRoot16 (d.w0 12560 162) (d.w1 12560 162)
          (d.w2 12560 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12560 : ℝ) ^ 16 *
        (((1895189967 / 100000000000000000000) : ℝ) + ((1348391407 / 100000000000000000000)) * (126 / 100) + 2 * ((492668549 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12560) *
          (32 * (((1895189967 / 100000000000000000000) : ℝ) + (1348391407 / 100000000000000000000) + (492668549 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12560

/-! A coarse bound on the actual paper statistics constant at dimension 12561. -/
namespace BstLean.Part266.Row12561
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12559 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12559 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12559 128 ≤ (12813 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12813 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12561) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12561 : ℕ))
    (by norm_num : (12561 : ℕ) ≤ 16384)
  have ht : paperTail256 12561 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12561 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12561 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12561 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12561 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12561 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12559 128 * √(2 / (12561 : ℝ)) *
      (√(12561 : ℝ) + paperT0 12561 + paperTail256 12561) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12561 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12561 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12561 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12559 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12559 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12561 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12561

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12561
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12561 (61 / 100) 162 (17 / (100 * 12561)) (26 / (10 * 12561)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12561 (61 / 100) 162 (17 / (100 * 12561)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (492545467 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (19606141 / 12500000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5590626357 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12561 / 12561 * (61 / 100)) ^ 4 * inverseRadius8 (12561 - 1) /
            envelopeGap 12561 (61 / 100) 162 (17 / (100 * 12561)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12561

namespace BstLean.Part266.Row12561
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12561 162 ≤ (2355272249 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12561 162 ≤ (1571517493 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (18885741 / 50000000000000000)
  w0 : (tableEnvelope C).w0 12561 162 ≤ (1894737 / 100000000000000000)
  w1 : (tableEnvelope C).w1 12561 162 ≤ (168508651 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 12561 162 ≤ (492550883 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (492545467 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (492545467 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (19606141 / 12500000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5590626357 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((919713 / 250000000) : ℝ) ≤ √(17 / (100 * 12561) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12561) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2219336539 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (2475261413 / 62500000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12561) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12561) ≤ (56293829 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12561) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12561 * (162 : ℝ) ^ 2 + 26 / (10 * 12561) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12561) : ℝ)) (tA 12561 * 162 ^ 2 + 26 / (10 * 12561)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((919713 / 250000000))) * ((492545467 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((919713 / 250000000)) ^ 3) * ((19606141 / 12500000000000000000000))) + ((5590626357 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((919713 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12561) : ℝ)) d.D d.V d.P (√(tA 12561) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((919713 / 250000000)) ^ 2 * (((2219336539 / 1000000000000000)) * ((2475261413 / 62500000000000000)))) + ((5590626357 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12561) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((919713 / 250000000)) * ((492545467 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12561) : ℝ)) (tA 12561 * 162 ^ 2 + 26 / (10 * 12561)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((492545467 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((919713 / 250000000)) ^ 2) * ((19606141 / 12500000000000000000000)) + ((5590626357 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12561) : ℝ)) (√(26 / (10 * 12561) : ℝ)) d.D d.V d.P (√(tA 12561) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((919713 / 250000000)) * (((2219336539 / 1000000000000000)) * ((2475261413 / 62500000000000000))) + ((5590626357 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12561) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((492545467 / 100000000000000000000) : ℝ) + ((5590626357 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12561

namespace BstLean.Part266.Row12561
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12561 162 ∧
    0 ≤ (tableEnvelope C).f1 12561 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12561 162 ∧
    0 ≤ (tableEnvelope C).w1 12561 162 ∧ 0 ≤ (tableEnvelope C).w2 12561 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12561 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12561 162 ∧ 0 ≤ d.f1 12561 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12561 162 ∧ 0 ≤ d.w1 12561 162 ∧ 0 ≤ d.w2 12561 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12561 ≤ 2 * (228 / 100 : ℝ) / 12561 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12561 ≤ 2 * (370 / 100 : ℝ) / 12561 := by
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
    (completeRAData (tableEnvelope C) 12561 162).locationBound 12561 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12561 162).energyBound 12561 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12561 162) (d.f1 12561 162) d.f2 ≤
      32 * (((2355272249 / 500000000000000000) : ℝ) + (1571517493 / 1000000000000000000) + (18885741 / 50000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12561 162) (d.w1 12561 162)
      (d.w2 12561 162) ≤
      32 * (((1894737 / 100000000000000000) : ℝ) + (168508651 / 12500000000000000000) + (492550883 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12561 162) (d.f1 12561 162) d.f2 ≤
      ((2355272249 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2355272249 / 500000000000000000)) * ((1571517493 / 1000000000000000000)) * (126 / 100) +
      2 * (((1571517493 / 1000000000000000000)) ^ 2 + 2 * ((2355272249 / 500000000000000000)) * ((18885741 / 50000000000000000))) +
      6 * ((1571517493 / 1000000000000000000)) * ((18885741 / 50000000000000000)) * (126 / 100) + 8 * ((18885741 / 50000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12561 162) (d.f1 12561 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12561 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12561 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12561 162) (d.f1 12561 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12561 162) (d.w1 12561 162) (d.w2 12561 162)
  have hwexpr0 : 0 ≤ d.w0 12561 162 + d.w1 12561 162 * √(π / 2) +
      2 * d.w2 12561 162 + energyR16 12561 *
      radiusPolynomialRoot16 (d.w0 12561 162) (d.w1 12561 162) (d.w2 12561 162) := by
    positivity
  constructor
  · change (12561 : ℝ) ^ 8 * (mA 12561 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12561 162) (d.f1 12561 162) d.f2 + locationR16 12561 *
        radiusPolynomialRoot16 (d.f0 12561 162) (d.f1 12561 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12561 : ℝ) ^ 8 * (mA 12561 : ℝ) ^ 8 *
        ((((2355272249 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2355272249 / 500000000000000000)) * ((1571517493 / 1000000000000000000)) * (126 / 100) +
          2 * (((1571517493 / 1000000000000000000)) ^ 2 + 2 * ((2355272249 / 500000000000000000)) * ((18885741 / 50000000000000000))) +
          6 * ((1571517493 / 1000000000000000000)) * ((18885741 / 50000000000000000)) * (126 / 100) + 8 * ((18885741 / 50000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12561) *
          (32 * (((2355272249 / 500000000000000000) : ℝ) + (1571517493 / 1000000000000000000) + (18885741 / 50000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12561 : ℝ) ^ 16 *
      (d.w0 12561 162 + d.w1 12561 162 * √(π / 2) + 2 * d.w2 12561 162 +
        energyR16 12561 * radiusPolynomialRoot16 (d.w0 12561 162) (d.w1 12561 162)
          (d.w2 12561 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12561 : ℝ) ^ 16 *
        (((1894737 / 100000000000000000) : ℝ) + ((168508651 / 12500000000000000000)) * (126 / 100) + 2 * ((492550883 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12561) *
          (32 * (((1894737 / 100000000000000000) : ℝ) + (168508651 / 12500000000000000000) + (492550883 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12561

/-! A coarse bound on the actual paper statistics constant at dimension 12562. -/
namespace BstLean.Part266.Row12562
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12560 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12560 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12560 128 ≤ (12814 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12814 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12562) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12562 : ℕ))
    (by norm_num : (12562 : ℕ) ≤ 16384)
  have ht : paperTail256 12562 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12562 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12562 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12562 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12562 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12562 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12560 128 * √(2 / (12562 : ℝ)) *
      (√(12562 : ℝ) + paperT0 12562 + paperTail256 12562) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12562 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12562 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12562 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12560 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12560 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12562 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12562

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12562
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12562 (61 / 100) 162 (17 / (100 * 12562)) (26 / (10 * 12562)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12562 (61 / 100) 162 (17 / (100 * 12562)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (492427843 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (39199797 / 25000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5587032009 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12562 / 12562 * (61 / 100)) ^ 4 * inverseRadius8 (12562 - 1) /
            envelopeGap 12562 (61 / 100) 162 (17 / (100 * 12562)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12562

namespace BstLean.Part266.Row12562
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12562 162 ≤ (4709609139 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12562 162 ≤ (785602613 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (377639709 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12562 162 ≤ (1894284953 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12562 162 ≤ (269549497 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12562 162 ≤ (61554157 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (492427843 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (492427843 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (39199797 / 25000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5587032009 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((735741 / 200000000) : ℝ) ≤ √(17 / (100 * 12562) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12562) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (88762861 / 40000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1237433663 / 31250000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12562) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12562) ≤ (22515739 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12562) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12562 * (162 : ℝ) ^ 2 + 26 / (10 * 12562) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12562) : ℝ)) (tA 12562 * 162 ^ 2 + 26 / (10 * 12562)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((735741 / 200000000))) * ((492427843 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((735741 / 200000000)) ^ 3) * ((39199797 / 25000000000000000000000))) + ((5587032009 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((735741 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12562) : ℝ)) d.D d.V d.P (√(tA 12562) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((735741 / 200000000)) ^ 2 * (((88762861 / 40000000000000)) * ((1237433663 / 31250000000000000)))) + ((5587032009 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12562) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((735741 / 200000000)) * ((492427843 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12562) : ℝ)) (tA 12562 * 162 ^ 2 + 26 / (10 * 12562)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((492427843 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((735741 / 200000000)) ^ 2) * ((39199797 / 25000000000000000000000)) + ((5587032009 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12562) : ℝ)) (√(26 / (10 * 12562) : ℝ)) d.D d.V d.P (√(tA 12562) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((735741 / 200000000)) * (((88762861 / 40000000000000)) * ((1237433663 / 31250000000000000))) + ((5587032009 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12562) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((492427843 / 100000000000000000000) : ℝ) + ((5587032009 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12562

namespace BstLean.Part266.Row12562
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12562 162 ∧
    0 ≤ (tableEnvelope C).f1 12562 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12562 162 ∧
    0 ≤ (tableEnvelope C).w1 12562 162 ∧ 0 ≤ (tableEnvelope C).w2 12562 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12562 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12562 162 ∧ 0 ≤ d.f1 12562 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12562 162 ∧ 0 ≤ d.w1 12562 162 ∧ 0 ≤ d.w2 12562 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12562 ≤ 2 * (228 / 100 : ℝ) / 12562 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12562 ≤ 2 * (370 / 100 : ℝ) / 12562 := by
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
    (completeRAData (tableEnvelope C) 12562 162).locationBound 12562 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12562 162).energyBound 12562 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12562 162) (d.f1 12562 162) d.f2 ≤
      32 * (((4709609139 / 1000000000000000000) : ℝ) + (785602613 / 500000000000000000) + (377639709 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12562 162) (d.w1 12562 162)
      (d.w2 12562 162) ≤
      32 * (((1894284953 / 100000000000000000000) : ℝ) + (269549497 / 20000000000000000000) + (61554157 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12562 162) (d.f1 12562 162) d.f2 ≤
      ((4709609139 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4709609139 / 1000000000000000000)) * ((785602613 / 500000000000000000)) * (126 / 100) +
      2 * (((785602613 / 500000000000000000)) ^ 2 + 2 * ((4709609139 / 1000000000000000000)) * ((377639709 / 1000000000000000000))) +
      6 * ((785602613 / 500000000000000000)) * ((377639709 / 1000000000000000000)) * (126 / 100) + 8 * ((377639709 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12562 162) (d.f1 12562 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12562 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12562 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12562 162) (d.f1 12562 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12562 162) (d.w1 12562 162) (d.w2 12562 162)
  have hwexpr0 : 0 ≤ d.w0 12562 162 + d.w1 12562 162 * √(π / 2) +
      2 * d.w2 12562 162 + energyR16 12562 *
      radiusPolynomialRoot16 (d.w0 12562 162) (d.w1 12562 162) (d.w2 12562 162) := by
    positivity
  constructor
  · change (12562 : ℝ) ^ 8 * (mA 12562 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12562 162) (d.f1 12562 162) d.f2 + locationR16 12562 *
        radiusPolynomialRoot16 (d.f0 12562 162) (d.f1 12562 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12562 : ℝ) ^ 8 * (mA 12562 : ℝ) ^ 8 *
        ((((4709609139 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4709609139 / 1000000000000000000)) * ((785602613 / 500000000000000000)) * (126 / 100) +
          2 * (((785602613 / 500000000000000000)) ^ 2 + 2 * ((4709609139 / 1000000000000000000)) * ((377639709 / 1000000000000000000))) +
          6 * ((785602613 / 500000000000000000)) * ((377639709 / 1000000000000000000)) * (126 / 100) + 8 * ((377639709 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12562) *
          (32 * (((4709609139 / 1000000000000000000) : ℝ) + (785602613 / 500000000000000000) + (377639709 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12562 : ℝ) ^ 16 *
      (d.w0 12562 162 + d.w1 12562 162 * √(π / 2) + 2 * d.w2 12562 162 +
        energyR16 12562 * radiusPolynomialRoot16 (d.w0 12562 162) (d.w1 12562 162)
          (d.w2 12562 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12562 : ℝ) ^ 16 *
        (((1894284953 / 100000000000000000000) : ℝ) + ((269549497 / 20000000000000000000)) * (126 / 100) + 2 * ((61554157 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12562) *
          (32 * (((1894284953 / 100000000000000000000) : ℝ) + (269549497 / 20000000000000000000) + (61554157 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12562

/-! A coarse bound on the actual paper statistics constant at dimension 12563. -/
namespace BstLean.Part266.Row12563
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12561 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12561 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12561 128 ≤ (12815 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12815 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12563) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12563 : ℕ))
    (by norm_num : (12563 : ℕ) ≤ 16384)
  have ht : paperTail256 12563 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12563 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12563 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12563 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12563 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12563 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12561 128 * √(2 / (12563 : ℝ)) *
      (√(12563 : ℝ) + paperT0 12563 + paperTail256 12563) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12563 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12563 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12563 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12561 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12561 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12563 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12563

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12563
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12563 (61 / 100) 162 (17 / (100 * 12563)) (26 / (10 * 12563)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12563 (61 / 100) 162 (17 / (100 * 12563)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (30769391 / 6250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (783746339 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5583440263 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12563 / 12563 * (61 / 100)) ^ 4 * inverseRadius8 (12563 - 1) /
            envelopeGap 12563 (61 / 100) 162 (17 / (100 * 12563)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12563

namespace BstLean.Part266.Row12563
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12563 162 ≤ (4708670409 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12563 162 ≤ (1570892207 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (377564517 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12563 162 ≤ (1893832301 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12563 162 ≤ (269485101 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12563 162 ≤ (98463133 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (30769391 / 6250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (30769391 / 6250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (783746339 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5583440263 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3678559 / 1000000000) : ℝ) ≤ √(17 / (100 * 12563) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12563) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2218806563 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39591573321 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12563) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12563) ≤ (56284867 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12563) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12563 * (162 : ℝ) ^ 2 + 26 / (10 * 12563) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12563) : ℝ)) (tA 12563 * 162 ^ 2 + 26 / (10 * 12563)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3678559 / 1000000000))) * ((30769391 / 6250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3678559 / 1000000000)) ^ 3) * ((783746339 / 500000000000000000000000))) + ((5583440263 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3678559 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12563) : ℝ)) d.D d.V d.P (√(tA 12563) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3678559 / 1000000000)) ^ 2 * (((2218806563 / 1000000000000000)) * ((39591573321 / 1000000000000000000)))) + ((5583440263 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12563) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3678559 / 1000000000)) * ((30769391 / 6250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12563) : ℝ)) (tA 12563 * 162 ^ 2 + 26 / (10 * 12563)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((30769391 / 6250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3678559 / 1000000000)) ^ 2) * ((783746339 / 500000000000000000000000)) + ((5583440263 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12563) : ℝ)) (√(26 / (10 * 12563) : ℝ)) d.D d.V d.P (√(tA 12563) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3678559 / 1000000000)) * (((2218806563 / 1000000000000000)) * ((39591573321 / 1000000000000000000))) + ((5583440263 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12563) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((30769391 / 6250000000000000000) : ℝ) + ((5583440263 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12563

namespace BstLean.Part266.Row12563
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12563 162 ∧
    0 ≤ (tableEnvelope C).f1 12563 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12563 162 ∧
    0 ≤ (tableEnvelope C).w1 12563 162 ∧ 0 ≤ (tableEnvelope C).w2 12563 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12563 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12563 162 ∧ 0 ≤ d.f1 12563 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12563 162 ∧ 0 ≤ d.w1 12563 162 ∧ 0 ≤ d.w2 12563 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12563 ≤ 2 * (228 / 100 : ℝ) / 12563 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12563 ≤ 2 * (370 / 100 : ℝ) / 12563 := by
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
    (completeRAData (tableEnvelope C) 12563 162).locationBound 12563 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12563 162).energyBound 12563 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12563 162) (d.f1 12563 162) d.f2 ≤
      32 * (((4708670409 / 1000000000000000000) : ℝ) + (1570892207 / 1000000000000000000) + (377564517 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12563 162) (d.w1 12563 162)
      (d.w2 12563 162) ≤
      32 * (((1893832301 / 100000000000000000000) : ℝ) + (269485101 / 20000000000000000000) + (98463133 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12563 162) (d.f1 12563 162) d.f2 ≤
      ((4708670409 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4708670409 / 1000000000000000000)) * ((1570892207 / 1000000000000000000)) * (126 / 100) +
      2 * (((1570892207 / 1000000000000000000)) ^ 2 + 2 * ((4708670409 / 1000000000000000000)) * ((377564517 / 1000000000000000000))) +
      6 * ((1570892207 / 1000000000000000000)) * ((377564517 / 1000000000000000000)) * (126 / 100) + 8 * ((377564517 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12563 162) (d.f1 12563 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12563 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12563 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12563 162) (d.f1 12563 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12563 162) (d.w1 12563 162) (d.w2 12563 162)
  have hwexpr0 : 0 ≤ d.w0 12563 162 + d.w1 12563 162 * √(π / 2) +
      2 * d.w2 12563 162 + energyR16 12563 *
      radiusPolynomialRoot16 (d.w0 12563 162) (d.w1 12563 162) (d.w2 12563 162) := by
    positivity
  constructor
  · change (12563 : ℝ) ^ 8 * (mA 12563 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12563 162) (d.f1 12563 162) d.f2 + locationR16 12563 *
        radiusPolynomialRoot16 (d.f0 12563 162) (d.f1 12563 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12563 : ℝ) ^ 8 * (mA 12563 : ℝ) ^ 8 *
        ((((4708670409 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4708670409 / 1000000000000000000)) * ((1570892207 / 1000000000000000000)) * (126 / 100) +
          2 * (((1570892207 / 1000000000000000000)) ^ 2 + 2 * ((4708670409 / 1000000000000000000)) * ((377564517 / 1000000000000000000))) +
          6 * ((1570892207 / 1000000000000000000)) * ((377564517 / 1000000000000000000)) * (126 / 100) + 8 * ((377564517 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12563) *
          (32 * (((4708670409 / 1000000000000000000) : ℝ) + (1570892207 / 1000000000000000000) + (377564517 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12563 : ℝ) ^ 16 *
      (d.w0 12563 162 + d.w1 12563 162 * √(π / 2) + 2 * d.w2 12563 162 +
        energyR16 12563 * radiusPolynomialRoot16 (d.w0 12563 162) (d.w1 12563 162)
          (d.w2 12563 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12563 : ℝ) ^ 16 *
        (((1893832301 / 100000000000000000000) : ℝ) + ((269485101 / 20000000000000000000)) * (126 / 100) + 2 * ((98463133 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12563) *
          (32 * (((1893832301 / 100000000000000000000) : ℝ) + (269485101 / 20000000000000000000) + (98463133 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12563

/-! A coarse bound on the actual paper statistics constant at dimension 12564. -/
namespace BstLean.Part266.Row12564
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12562 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12562 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12562 128 ≤ (12816 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12816 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12564) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12564 : ℕ))
    (by norm_num : (12564 : ℕ) ≤ 16384)
  have ht : paperTail256 12564 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12564 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12564 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12564 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12564 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12564 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12562 128 * √(2 / (12564 : ℝ)) *
      (√(12564 : ℝ) + paperT0 12564 + paperTail256 12564) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12564 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12564 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12564 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12562 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12562 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12564 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12564

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12564
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12564 (61 / 100) 162 (17 / (100 * 12564)) (26 / (10 * 12564)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12564 (61 / 100) 162 (17 / (100 * 12564)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (246096353 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (62679747 / 40000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2789925559 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12564 / 12564 * (61 / 100)) ^ 4 * inverseRadius8 (12564 - 1) /
            envelopeGap 12564 (61 / 100) 162 (17 / (100 * 12564)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12564

namespace BstLean.Part266.Row12564
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12564 162 ≤ (941546401 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12564 162 ≤ (196322411 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (377489347 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12564 162 ≤ (946689903 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12564 162 ≤ (84193977 / 6250000000000000000)
  w2 : (tableEnvelope C).w2 12564 162 ≤ (15381191 / 3125000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (246096353 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (246096353 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (62679747 / 40000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2789925559 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3678413 / 1000000000) : ℝ) ≤ √(17 / (100 * 12564) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12564) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (554635413 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4948158867 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12564) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12564) ≤ (56280387 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12564) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12564 * (162 : ℝ) ^ 2 + 26 / (10 * 12564) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12564) : ℝ)) (tA 12564 * 162 ^ 2 + 26 / (10 * 12564)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3678413 / 1000000000))) * ((246096353 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3678413 / 1000000000)) ^ 3) * ((62679747 / 40000000000000000000000))) + ((2789925559 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3678413 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12564) : ℝ)) d.D d.V d.P (√(tA 12564) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3678413 / 1000000000)) ^ 2 * (((554635413 / 250000000000000)) * ((4948158867 / 125000000000000000)))) + ((2789925559 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12564) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3678413 / 1000000000)) * ((246096353 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12564) : ℝ)) (tA 12564 * 162 ^ 2 + 26 / (10 * 12564)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((246096353 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3678413 / 1000000000)) ^ 2) * ((62679747 / 40000000000000000000000)) + ((2789925559 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12564) : ℝ)) (√(26 / (10 * 12564) : ℝ)) d.D d.V d.P (√(tA 12564) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3678413 / 1000000000)) * (((554635413 / 250000000000000)) * ((4948158867 / 125000000000000000))) + ((2789925559 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12564) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((246096353 / 50000000000000000000) : ℝ) + ((2789925559 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12564

namespace BstLean.Part266.Row12564
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12564 162 ∧
    0 ≤ (tableEnvelope C).f1 12564 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12564 162 ∧
    0 ≤ (tableEnvelope C).w1 12564 162 ∧ 0 ≤ (tableEnvelope C).w2 12564 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12564 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12564 162 ∧ 0 ≤ d.f1 12564 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12564 162 ∧ 0 ≤ d.w1 12564 162 ∧ 0 ≤ d.w2 12564 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12564 ≤ 2 * (228 / 100 : ℝ) / 12564 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12564 ≤ 2 * (370 / 100 : ℝ) / 12564 := by
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
    (completeRAData (tableEnvelope C) 12564 162).locationBound 12564 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12564 162).energyBound 12564 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12564 162) (d.f1 12564 162) d.f2 ≤
      32 * (((941546401 / 200000000000000000) : ℝ) + (196322411 / 125000000000000000) + (377489347 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12564 162) (d.w1 12564 162)
      (d.w2 12564 162) ≤
      32 * (((946689903 / 50000000000000000000) : ℝ) + (84193977 / 6250000000000000000) + (15381191 / 3125000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12564 162) (d.f1 12564 162) d.f2 ≤
      ((941546401 / 200000000000000000) : ℝ) ^ 2 + 2 * ((941546401 / 200000000000000000)) * ((196322411 / 125000000000000000)) * (126 / 100) +
      2 * (((196322411 / 125000000000000000)) ^ 2 + 2 * ((941546401 / 200000000000000000)) * ((377489347 / 1000000000000000000))) +
      6 * ((196322411 / 125000000000000000)) * ((377489347 / 1000000000000000000)) * (126 / 100) + 8 * ((377489347 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12564 162) (d.f1 12564 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12564 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12564 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12564 162) (d.f1 12564 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12564 162) (d.w1 12564 162) (d.w2 12564 162)
  have hwexpr0 : 0 ≤ d.w0 12564 162 + d.w1 12564 162 * √(π / 2) +
      2 * d.w2 12564 162 + energyR16 12564 *
      radiusPolynomialRoot16 (d.w0 12564 162) (d.w1 12564 162) (d.w2 12564 162) := by
    positivity
  constructor
  · change (12564 : ℝ) ^ 8 * (mA 12564 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12564 162) (d.f1 12564 162) d.f2 + locationR16 12564 *
        radiusPolynomialRoot16 (d.f0 12564 162) (d.f1 12564 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12564 : ℝ) ^ 8 * (mA 12564 : ℝ) ^ 8 *
        ((((941546401 / 200000000000000000) : ℝ) ^ 2 + 2 * ((941546401 / 200000000000000000)) * ((196322411 / 125000000000000000)) * (126 / 100) +
          2 * (((196322411 / 125000000000000000)) ^ 2 + 2 * ((941546401 / 200000000000000000)) * ((377489347 / 1000000000000000000))) +
          6 * ((196322411 / 125000000000000000)) * ((377489347 / 1000000000000000000)) * (126 / 100) + 8 * ((377489347 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12564) *
          (32 * (((941546401 / 200000000000000000) : ℝ) + (196322411 / 125000000000000000) + (377489347 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12564 : ℝ) ^ 16 *
      (d.w0 12564 162 + d.w1 12564 162 * √(π / 2) + 2 * d.w2 12564 162 +
        energyR16 12564 * radiusPolynomialRoot16 (d.w0 12564 162) (d.w1 12564 162)
          (d.w2 12564 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12564 : ℝ) ^ 16 *
        (((946689903 / 50000000000000000000) : ℝ) + ((84193977 / 6250000000000000000)) * (126 / 100) + 2 * ((15381191 / 3125000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12564) *
          (32 * (((946689903 / 50000000000000000000) : ℝ) + (84193977 / 6250000000000000000) + (15381191 / 3125000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12564

/-! A coarse bound on the actual paper statistics constant at dimension 12565. -/
namespace BstLean.Part266.Row12565
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12563 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12563 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12563 128 ≤ (12817 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12817 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12565) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12565 : ℕ))
    (by norm_num : (12565 : ℕ) ≤ 16384)
  have ht : paperTail256 12565 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12565 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12565 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12565 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12565 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12565 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12563 128 * √(2 / (12565 : ℝ)) *
      (√(12565 : ℝ) + paperT0 12565 + paperTail256 12565) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12565 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12565 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12565 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12563 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12563 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12565 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12565

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12565
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12565 (61 / 100) 162 (17 / (100 * 12565)) (26 / (10 * 12565)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12565 (61 / 100) 162 (17 / (100 * 12565)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (246037597 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1566494871 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5576264571 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12565 / 12565 * (61 / 100)) ^ 4 * inverseRadius8 (12565 - 1) /
            envelopeGap 12565 (61 / 100) 162 (17 / (100 * 12565)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12565

namespace BstLean.Part266.Row12565
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12565 162 ≤ (4706797623 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12565 162 ≤ (1570267327 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (377414303 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12565 162 ≤ (189292823 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 12565 162 ≤ (336695559 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12565 162 ≤ (123020149 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (246037597 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (246037597 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1566494871 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5576264571 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1839133 / 500000000) : ℝ) ≤ √(17 / (100 * 12565) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12565) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (554569199 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1978948503 / 50000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12565) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12565) ≤ (14068977 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12565) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12565 * (162 : ℝ) ^ 2 + 26 / (10 * 12565) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12565) : ℝ)) (tA 12565 * 162 ^ 2 + 26 / (10 * 12565)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1839133 / 500000000))) * ((246037597 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1839133 / 500000000)) ^ 3) * ((1566494871 / 1000000000000000000000000))) + ((5576264571 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1839133 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12565) : ℝ)) d.D d.V d.P (√(tA 12565) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1839133 / 500000000)) ^ 2 * (((554569199 / 250000000000000)) * ((1978948503 / 50000000000000000)))) + ((5576264571 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12565) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1839133 / 500000000)) * ((246037597 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12565) : ℝ)) (tA 12565 * 162 ^ 2 + 26 / (10 * 12565)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((246037597 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1839133 / 500000000)) ^ 2) * ((1566494871 / 1000000000000000000000000)) + ((5576264571 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12565) : ℝ)) (√(26 / (10 * 12565) : ℝ)) d.D d.V d.P (√(tA 12565) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1839133 / 500000000)) * (((554569199 / 250000000000000)) * ((1978948503 / 50000000000000000))) + ((5576264571 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12565) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((246037597 / 50000000000000000000) : ℝ) + ((5576264571 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12565

namespace BstLean.Part266.Row12565
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12565 162 ∧
    0 ≤ (tableEnvelope C).f1 12565 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12565 162 ∧
    0 ≤ (tableEnvelope C).w1 12565 162 ∧ 0 ≤ (tableEnvelope C).w2 12565 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12565 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12565 162 ∧ 0 ≤ d.f1 12565 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12565 162 ∧ 0 ≤ d.w1 12565 162 ∧ 0 ≤ d.w2 12565 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12565 ≤ 2 * (228 / 100 : ℝ) / 12565 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12565 ≤ 2 * (370 / 100 : ℝ) / 12565 := by
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
    (completeRAData (tableEnvelope C) 12565 162).locationBound 12565 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12565 162).energyBound 12565 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12565 162) (d.f1 12565 162) d.f2 ≤
      32 * (((4706797623 / 1000000000000000000) : ℝ) + (1570267327 / 1000000000000000000) + (377414303 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12565 162) (d.w1 12565 162)
      (d.w2 12565 162) ≤
      32 * (((189292823 / 10000000000000000000) : ℝ) + (336695559 / 25000000000000000000) + (123020149 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12565 162) (d.f1 12565 162) d.f2 ≤
      ((4706797623 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4706797623 / 1000000000000000000)) * ((1570267327 / 1000000000000000000)) * (126 / 100) +
      2 * (((1570267327 / 1000000000000000000)) ^ 2 + 2 * ((4706797623 / 1000000000000000000)) * ((377414303 / 1000000000000000000))) +
      6 * ((1570267327 / 1000000000000000000)) * ((377414303 / 1000000000000000000)) * (126 / 100) + 8 * ((377414303 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12565 162) (d.f1 12565 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12565 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12565 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12565 162) (d.f1 12565 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12565 162) (d.w1 12565 162) (d.w2 12565 162)
  have hwexpr0 : 0 ≤ d.w0 12565 162 + d.w1 12565 162 * √(π / 2) +
      2 * d.w2 12565 162 + energyR16 12565 *
      radiusPolynomialRoot16 (d.w0 12565 162) (d.w1 12565 162) (d.w2 12565 162) := by
    positivity
  constructor
  · change (12565 : ℝ) ^ 8 * (mA 12565 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12565 162) (d.f1 12565 162) d.f2 + locationR16 12565 *
        radiusPolynomialRoot16 (d.f0 12565 162) (d.f1 12565 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12565 : ℝ) ^ 8 * (mA 12565 : ℝ) ^ 8 *
        ((((4706797623 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4706797623 / 1000000000000000000)) * ((1570267327 / 1000000000000000000)) * (126 / 100) +
          2 * (((1570267327 / 1000000000000000000)) ^ 2 + 2 * ((4706797623 / 1000000000000000000)) * ((377414303 / 1000000000000000000))) +
          6 * ((1570267327 / 1000000000000000000)) * ((377414303 / 1000000000000000000)) * (126 / 100) + 8 * ((377414303 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12565) *
          (32 * (((4706797623 / 1000000000000000000) : ℝ) + (1570267327 / 1000000000000000000) + (377414303 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12565 : ℝ) ^ 16 *
      (d.w0 12565 162 + d.w1 12565 162 * √(π / 2) + 2 * d.w2 12565 162 +
        energyR16 12565 * radiusPolynomialRoot16 (d.w0 12565 162) (d.w1 12565 162)
          (d.w2 12565 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12565 : ℝ) ^ 16 *
        (((189292823 / 10000000000000000000) : ℝ) + ((336695559 / 25000000000000000000)) * (126 / 100) + 2 * ((123020149 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12565) *
          (32 * (((189292823 / 10000000000000000000) : ℝ) + (336695559 / 25000000000000000000) + (123020149 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12565

/-! A coarse bound on the actual paper statistics constant at dimension 12566. -/
namespace BstLean.Part266.Row12566
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12564 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12564 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12564 128 ≤ (12818 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12818 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12566) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12566 : ℕ))
    (by norm_num : (12566 : ℕ) ≤ 16384)
  have ht : paperTail256 12566 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12566 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12566 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12566 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12566 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12566 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12564 128 * √(2 / (12566 : ℝ)) *
      (√(12566 : ℝ) + paperT0 12566 + paperTail256 12566) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12566 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12566 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12566 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12564 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12564 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12566 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12566

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12566
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12566 (61 / 100) 162 (17 / (100 * 12566)) (26 / (10 * 12566)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12566 (61 / 100) 162 (17 / (100 * 12566)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (491957719 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (313199253 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (278634031 / 50000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12566 / 12566 * (61 / 100)) ^ 4 * inverseRadius8 (12566 - 1) /
            envelopeGap 12566 (61 / 100) 162 (17 / (100 * 12566)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12566

namespace BstLean.Part266.Row12566
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12566 162 ≤ (4705859871 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12566 162 ≤ (392488653 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (377339179 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12566 162 ≤ (37849521 / 2000000000000000000)
  w1 : (tableEnvelope C).w1 12566 162 ≤ (1346460581 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12566 162 ≤ (245981559 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (491957719 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (491957719 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (313199253 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (278634031 / 50000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((91953 / 25000000) : ℝ) ≤ √(17 / (100 * 12566) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12566) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2218011991 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9893167671 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12566) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12566) ≤ (112542859 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12566) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12566 * (162 : ℝ) ^ 2 + 26 / (10 * 12566) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12566) : ℝ)) (tA 12566 * 162 ^ 2 + 26 / (10 * 12566)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((91953 / 25000000))) * ((491957719 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((91953 / 25000000)) ^ 3) * ((313199253 / 200000000000000000000000))) + ((278634031 / 50000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((91953 / 25000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12566) : ℝ)) d.D d.V d.P (√(tA 12566) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((91953 / 25000000)) ^ 2 * (((2218011991 / 1000000000000000)) * ((9893167671 / 250000000000000000)))) + ((278634031 / 50000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12566) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((91953 / 25000000)) * ((491957719 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12566) : ℝ)) (tA 12566 * 162 ^ 2 + 26 / (10 * 12566)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((491957719 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((91953 / 25000000)) ^ 2) * ((313199253 / 200000000000000000000000)) + ((278634031 / 50000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12566) : ℝ)) (√(26 / (10 * 12566) : ℝ)) d.D d.V d.P (√(tA 12566) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((91953 / 25000000)) * (((2218011991 / 1000000000000000)) * ((9893167671 / 250000000000000000))) + ((278634031 / 50000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12566) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((491957719 / 100000000000000000000) : ℝ) + ((278634031 / 50000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12566

namespace BstLean.Part266.Row12566
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12566 162 ∧
    0 ≤ (tableEnvelope C).f1 12566 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12566 162 ∧
    0 ≤ (tableEnvelope C).w1 12566 162 ∧ 0 ≤ (tableEnvelope C).w2 12566 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12566 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12566 162 ∧ 0 ≤ d.f1 12566 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12566 162 ∧ 0 ≤ d.w1 12566 162 ∧ 0 ≤ d.w2 12566 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12566 ≤ 2 * (228 / 100 : ℝ) / 12566 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12566 ≤ 2 * (370 / 100 : ℝ) / 12566 := by
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
    (completeRAData (tableEnvelope C) 12566 162).locationBound 12566 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12566 162).energyBound 12566 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12566 162) (d.f1 12566 162) d.f2 ≤
      32 * (((4705859871 / 1000000000000000000) : ℝ) + (392488653 / 250000000000000000) + (377339179 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12566 162) (d.w1 12566 162)
      (d.w2 12566 162) ≤
      32 * (((37849521 / 2000000000000000000) : ℝ) + (1346460581 / 100000000000000000000) + (245981559 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12566 162) (d.f1 12566 162) d.f2 ≤
      ((4705859871 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4705859871 / 1000000000000000000)) * ((392488653 / 250000000000000000)) * (126 / 100) +
      2 * (((392488653 / 250000000000000000)) ^ 2 + 2 * ((4705859871 / 1000000000000000000)) * ((377339179 / 1000000000000000000))) +
      6 * ((392488653 / 250000000000000000)) * ((377339179 / 1000000000000000000)) * (126 / 100) + 8 * ((377339179 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12566 162) (d.f1 12566 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12566 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12566 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12566 162) (d.f1 12566 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12566 162) (d.w1 12566 162) (d.w2 12566 162)
  have hwexpr0 : 0 ≤ d.w0 12566 162 + d.w1 12566 162 * √(π / 2) +
      2 * d.w2 12566 162 + energyR16 12566 *
      radiusPolynomialRoot16 (d.w0 12566 162) (d.w1 12566 162) (d.w2 12566 162) := by
    positivity
  constructor
  · change (12566 : ℝ) ^ 8 * (mA 12566 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12566 162) (d.f1 12566 162) d.f2 + locationR16 12566 *
        radiusPolynomialRoot16 (d.f0 12566 162) (d.f1 12566 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12566 : ℝ) ^ 8 * (mA 12566 : ℝ) ^ 8 *
        ((((4705859871 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4705859871 / 1000000000000000000)) * ((392488653 / 250000000000000000)) * (126 / 100) +
          2 * (((392488653 / 250000000000000000)) ^ 2 + 2 * ((4705859871 / 1000000000000000000)) * ((377339179 / 1000000000000000000))) +
          6 * ((392488653 / 250000000000000000)) * ((377339179 / 1000000000000000000)) * (126 / 100) + 8 * ((377339179 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12566) *
          (32 * (((4705859871 / 1000000000000000000) : ℝ) + (392488653 / 250000000000000000) + (377339179 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12566 : ℝ) ^ 16 *
      (d.w0 12566 162 + d.w1 12566 162 * √(π / 2) + 2 * d.w2 12566 162 +
        energyR16 12566 * radiusPolynomialRoot16 (d.w0 12566 162) (d.w1 12566 162)
          (d.w2 12566 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12566 : ℝ) ^ 16 *
        (((37849521 / 2000000000000000000) : ℝ) + ((1346460581 / 100000000000000000000)) * (126 / 100) + 2 * ((245981559 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12566) *
          (32 * (((37849521 / 2000000000000000000) : ℝ) + (1346460581 / 100000000000000000000) + (245981559 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12566

/-! A coarse bound on the actual paper statistics constant at dimension 12567. -/
namespace BstLean.Part266.Row12567
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12565 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12565 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12565 128 ≤ (12819 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12819 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12567) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12567 : ℕ))
    (by norm_num : (12567 : ℕ) ≤ 16384)
  have ht : paperTail256 12567 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12567 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12567 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12567 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12567 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12567 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12565 128 * √(2 / (12567 : ℝ)) *
      (√(12567 : ℝ) + paperT0 12567 + paperTail256 12567) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12567 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12567 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12567 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12565 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12565 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12567 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12567

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12567
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12567 (61 / 100) 162 (17 / (100 * 12567)) (26 / (10 * 12567)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12567 (61 / 100) 162 (17 / (100 * 12567)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (245920141 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (782748929 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2784549631 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12567 / 12567 * (61 / 100)) ^ 4 * inverseRadius8 (12567 - 1) /
            envelopeGap 12567 (61 / 100) 162 (17 / (100 * 12567)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12567

namespace BstLean.Part266.Row12567
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12567 162 ≤ (4704926139 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12567 162 ≤ (313928571 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (377264181 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12567 162 ≤ (1892024789 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12567 162 ≤ (673069701 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12567 162 ≤ (491845677 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (245920141 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (245920141 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (782748929 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2784549631 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3677973 / 1000000000) : ℝ) ≤ √(17 / (100 * 12567) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12567) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (55443681 / 25000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39566372819 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12567) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12567) ≤ (7033369 / 62500000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12567) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12567 * (162 : ℝ) ^ 2 + 26 / (10 * 12567) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12567) : ℝ)) (tA 12567 * 162 ^ 2 + 26 / (10 * 12567)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3677973 / 1000000000))) * ((245920141 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3677973 / 1000000000)) ^ 3) * ((782748929 / 500000000000000000000000))) + ((2784549631 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3677973 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12567) : ℝ)) d.D d.V d.P (√(tA 12567) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3677973 / 1000000000)) ^ 2 * (((55443681 / 25000000000000)) * ((39566372819 / 1000000000000000000)))) + ((2784549631 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12567) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3677973 / 1000000000)) * ((245920141 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12567) : ℝ)) (tA 12567 * 162 ^ 2 + 26 / (10 * 12567)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((245920141 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3677973 / 1000000000)) ^ 2) * ((782748929 / 500000000000000000000000)) + ((2784549631 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12567) : ℝ)) (√(26 / (10 * 12567) : ℝ)) d.D d.V d.P (√(tA 12567) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3677973 / 1000000000)) * (((55443681 / 25000000000000)) * ((39566372819 / 1000000000000000000))) + ((2784549631 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12567) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((245920141 / 50000000000000000000) : ℝ) + ((2784549631 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12567

namespace BstLean.Part266.Row12567
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12567 162 ∧
    0 ≤ (tableEnvelope C).f1 12567 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12567 162 ∧
    0 ≤ (tableEnvelope C).w1 12567 162 ∧ 0 ≤ (tableEnvelope C).w2 12567 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12567 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12567 162 ∧ 0 ≤ d.f1 12567 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12567 162 ∧ 0 ≤ d.w1 12567 162 ∧ 0 ≤ d.w2 12567 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12567 ≤ 2 * (228 / 100 : ℝ) / 12567 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12567 ≤ 2 * (370 / 100 : ℝ) / 12567 := by
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
    (completeRAData (tableEnvelope C) 12567 162).locationBound 12567 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12567 162).energyBound 12567 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12567 162) (d.f1 12567 162) d.f2 ≤
      32 * (((4704926139 / 1000000000000000000) : ℝ) + (313928571 / 200000000000000000) + (377264181 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12567 162) (d.w1 12567 162)
      (d.w2 12567 162) ≤
      32 * (((1892024789 / 100000000000000000000) : ℝ) + (673069701 / 50000000000000000000) + (491845677 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12567 162) (d.f1 12567 162) d.f2 ≤
      ((4704926139 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4704926139 / 1000000000000000000)) * ((313928571 / 200000000000000000)) * (126 / 100) +
      2 * (((313928571 / 200000000000000000)) ^ 2 + 2 * ((4704926139 / 1000000000000000000)) * ((377264181 / 1000000000000000000))) +
      6 * ((313928571 / 200000000000000000)) * ((377264181 / 1000000000000000000)) * (126 / 100) + 8 * ((377264181 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12567 162) (d.f1 12567 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12567 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12567 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12567 162) (d.f1 12567 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12567 162) (d.w1 12567 162) (d.w2 12567 162)
  have hwexpr0 : 0 ≤ d.w0 12567 162 + d.w1 12567 162 * √(π / 2) +
      2 * d.w2 12567 162 + energyR16 12567 *
      radiusPolynomialRoot16 (d.w0 12567 162) (d.w1 12567 162) (d.w2 12567 162) := by
    positivity
  constructor
  · change (12567 : ℝ) ^ 8 * (mA 12567 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12567 162) (d.f1 12567 162) d.f2 + locationR16 12567 *
        radiusPolynomialRoot16 (d.f0 12567 162) (d.f1 12567 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12567 : ℝ) ^ 8 * (mA 12567 : ℝ) ^ 8 *
        ((((4704926139 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4704926139 / 1000000000000000000)) * ((313928571 / 200000000000000000)) * (126 / 100) +
          2 * (((313928571 / 200000000000000000)) ^ 2 + 2 * ((4704926139 / 1000000000000000000)) * ((377264181 / 1000000000000000000))) +
          6 * ((313928571 / 200000000000000000)) * ((377264181 / 1000000000000000000)) * (126 / 100) + 8 * ((377264181 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12567) *
          (32 * (((4704926139 / 1000000000000000000) : ℝ) + (313928571 / 200000000000000000) + (377264181 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12567 : ℝ) ^ 16 *
      (d.w0 12567 162 + d.w1 12567 162 * √(π / 2) + 2 * d.w2 12567 162 +
        energyR16 12567 * radiusPolynomialRoot16 (d.w0 12567 162) (d.w1 12567 162)
          (d.w2 12567 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12567 : ℝ) ^ 16 *
        (((1892024789 / 100000000000000000000) : ℝ) + ((673069701 / 50000000000000000000)) * (126 / 100) + 2 * ((491845677 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12567) *
          (32 * (((1892024789 / 100000000000000000000) : ℝ) + (673069701 / 50000000000000000000) + (491845677 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12567

/-! A coarse bound on the actual paper statistics constant at dimension 12568. -/
namespace BstLean.Part266.Row12568
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12566 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12566 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12566 128 ≤ (12820 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12820 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12568) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12568 : ℕ))
    (by norm_num : (12568 : ℕ) ≤ 16384)
  have ht : paperTail256 12568 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12568 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12568 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12568 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12568 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12568 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12566 128 * √(2 / (12568 : ℝ)) *
      (√(12568 : ℝ) + paperT0 12568 + paperTail256 12568) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12568 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12568 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12568 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12566 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12566 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12568 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12568

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12568
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12568 (61 / 100) 162 (17 / (100 * 12568)) (26 / (10 * 12568)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12568 (61 / 100) 162 (17 / (100 * 12568)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (245861441 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1564999649 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5565520497 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12568 / 12568 * (61 / 100)) ^ 4 * inverseRadius8 (12568 - 1) /
            envelopeGap 12568 (61 / 100) 162 (17 / (100 * 12568)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12568

namespace BstLean.Part266.Row12568
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12568 162 ≤ (2351994519 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12568 162 ≤ (784665173 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (377189103 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12568 162 ≤ (472893231 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12568 162 ≤ (672908983 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12568 162 ≤ (245864137 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (245861441 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (245861441 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1564999649 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5565520497 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3677827 / 1000000000) : ℝ) ≤ √(17 / (100 * 12568) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12568) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1108741271 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19780038227 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12568) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12568) ≤ (2250499 / 20000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12568) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12568 * (162 : ℝ) ^ 2 + 26 / (10 * 12568) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12568) : ℝ)) (tA 12568 * 162 ^ 2 + 26 / (10 * 12568)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3677827 / 1000000000))) * ((245861441 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3677827 / 1000000000)) ^ 3) * ((1564999649 / 1000000000000000000000000))) + ((5565520497 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3677827 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12568) : ℝ)) d.D d.V d.P (√(tA 12568) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3677827 / 1000000000)) ^ 2 * (((1108741271 / 500000000000000)) * ((19780038227 / 500000000000000000)))) + ((5565520497 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12568) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3677827 / 1000000000)) * ((245861441 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12568) : ℝ)) (tA 12568 * 162 ^ 2 + 26 / (10 * 12568)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((245861441 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3677827 / 1000000000)) ^ 2) * ((1564999649 / 1000000000000000000000000)) + ((5565520497 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12568) : ℝ)) (√(26 / (10 * 12568) : ℝ)) d.D d.V d.P (√(tA 12568) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3677827 / 1000000000)) * (((1108741271 / 500000000000000)) * ((19780038227 / 500000000000000000))) + ((5565520497 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12568) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((245861441 / 50000000000000000000) : ℝ) + ((5565520497 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12568

namespace BstLean.Part266.Row12568
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12568 162 ∧
    0 ≤ (tableEnvelope C).f1 12568 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12568 162 ∧
    0 ≤ (tableEnvelope C).w1 12568 162 ∧ 0 ≤ (tableEnvelope C).w2 12568 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12568 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12568 162 ∧ 0 ≤ d.f1 12568 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12568 162 ∧ 0 ≤ d.w1 12568 162 ∧ 0 ≤ d.w2 12568 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12568 ≤ 2 * (228 / 100 : ℝ) / 12568 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12568 ≤ 2 * (370 / 100 : ℝ) / 12568 := by
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
    (completeRAData (tableEnvelope C) 12568 162).locationBound 12568 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12568 162).energyBound 12568 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12568 162) (d.f1 12568 162) d.f2 ≤
      32 * (((2351994519 / 500000000000000000) : ℝ) + (784665173 / 500000000000000000) + (377189103 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12568 162) (d.w1 12568 162)
      (d.w2 12568 162) ≤
      32 * (((472893231 / 25000000000000000000) : ℝ) + (672908983 / 50000000000000000000) + (245864137 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12568 162) (d.f1 12568 162) d.f2 ≤
      ((2351994519 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2351994519 / 500000000000000000)) * ((784665173 / 500000000000000000)) * (126 / 100) +
      2 * (((784665173 / 500000000000000000)) ^ 2 + 2 * ((2351994519 / 500000000000000000)) * ((377189103 / 1000000000000000000))) +
      6 * ((784665173 / 500000000000000000)) * ((377189103 / 1000000000000000000)) * (126 / 100) + 8 * ((377189103 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12568 162) (d.f1 12568 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12568 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12568 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12568 162) (d.f1 12568 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12568 162) (d.w1 12568 162) (d.w2 12568 162)
  have hwexpr0 : 0 ≤ d.w0 12568 162 + d.w1 12568 162 * √(π / 2) +
      2 * d.w2 12568 162 + energyR16 12568 *
      radiusPolynomialRoot16 (d.w0 12568 162) (d.w1 12568 162) (d.w2 12568 162) := by
    positivity
  constructor
  · change (12568 : ℝ) ^ 8 * (mA 12568 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12568 162) (d.f1 12568 162) d.f2 + locationR16 12568 *
        radiusPolynomialRoot16 (d.f0 12568 162) (d.f1 12568 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12568 : ℝ) ^ 8 * (mA 12568 : ℝ) ^ 8 *
        ((((2351994519 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2351994519 / 500000000000000000)) * ((784665173 / 500000000000000000)) * (126 / 100) +
          2 * (((784665173 / 500000000000000000)) ^ 2 + 2 * ((2351994519 / 500000000000000000)) * ((377189103 / 1000000000000000000))) +
          6 * ((784665173 / 500000000000000000)) * ((377189103 / 1000000000000000000)) * (126 / 100) + 8 * ((377189103 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12568) *
          (32 * (((2351994519 / 500000000000000000) : ℝ) + (784665173 / 500000000000000000) + (377189103 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12568 : ℝ) ^ 16 *
      (d.w0 12568 162 + d.w1 12568 162 * √(π / 2) + 2 * d.w2 12568 162 +
        energyR16 12568 * radiusPolynomialRoot16 (d.w0 12568 162) (d.w1 12568 162)
          (d.w2 12568 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12568 : ℝ) ^ 16 *
        (((472893231 / 25000000000000000000) : ℝ) + ((672908983 / 50000000000000000000)) * (126 / 100) + 2 * ((245864137 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12568) *
          (32 * (((472893231 / 25000000000000000000) : ℝ) + (672908983 / 50000000000000000000) + (245864137 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12568

/-! A coarse bound on the actual paper statistics constant at dimension 12569. -/
namespace BstLean.Part266.Row12569
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12567 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12567 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12567 128 ≤ (12821 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12821 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12569) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12569 : ℕ))
    (by norm_num : (12569 : ℕ) ≤ 16384)
  have ht : paperTail256 12569 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12569 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12569 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12569 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12569 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12569 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12567 128 * √(2 / (12569 : ℝ)) *
      (√(12569 : ℝ) + paperT0 12569 + paperTail256 12569) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12569 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12569 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12569 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12567 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12567 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12569 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12569

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12569
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12569 (61 / 100) 162 (17 / (100 * 12569)) (26 / (10 * 12569)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12569 (61 / 100) 162 (17 / (100 * 12569)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (6145069 / 1250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (782250819 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5561944321 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12569 / 12569 * (61 / 100)) ^ 4 * inverseRadius8 (12569 - 1) /
            envelopeGap 12569 (61 / 100) 162 (17 / (100 * 12569)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12569

namespace BstLean.Part266.Row12569
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12569 162 ≤ (4703052263 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12569 162 ≤ (1569017939 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (5892407 / 15625000000000000)
  w0 : (tableEnvelope C).w0 12569 162 ≤ (29548769 / 1562500000000000000)
  w1 : (tableEnvelope C).w1 12569 162 ≤ (1345496639 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12569 162 ≤ (122902727 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (6145069 / 1250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (6145069 / 1250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (782250819 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5561944321 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3677681 / 1000000000) : ℝ) ≤ √(17 / (100 * 12569) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12569) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2217217897 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3955378159 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12569) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12569) ≤ (112515997 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12569) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12569 * (162 : ℝ) ^ 2 + 26 / (10 * 12569) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12569) : ℝ)) (tA 12569 * 162 ^ 2 + 26 / (10 * 12569)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3677681 / 1000000000))) * ((6145069 / 1250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3677681 / 1000000000)) ^ 3) * ((782250819 / 500000000000000000000000))) + ((5561944321 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3677681 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12569) : ℝ)) d.D d.V d.P (√(tA 12569) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3677681 / 1000000000)) ^ 2 * (((2217217897 / 1000000000000000)) * ((3955378159 / 100000000000000000)))) + ((5561944321 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12569) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3677681 / 1000000000)) * ((6145069 / 1250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12569) : ℝ)) (tA 12569 * 162 ^ 2 + 26 / (10 * 12569)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((6145069 / 1250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3677681 / 1000000000)) ^ 2) * ((782250819 / 500000000000000000000000)) + ((5561944321 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12569) : ℝ)) (√(26 / (10 * 12569) : ℝ)) d.D d.V d.P (√(tA 12569) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3677681 / 1000000000)) * (((2217217897 / 1000000000000000)) * ((3955378159 / 100000000000000000))) + ((5561944321 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12569) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((6145069 / 1250000000000000000) : ℝ) + ((5561944321 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12569

namespace BstLean.Part266.Row12569
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12569 162 ∧
    0 ≤ (tableEnvelope C).f1 12569 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12569 162 ∧
    0 ≤ (tableEnvelope C).w1 12569 162 ∧ 0 ≤ (tableEnvelope C).w2 12569 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12569 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12569 162 ∧ 0 ≤ d.f1 12569 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12569 162 ∧ 0 ≤ d.w1 12569 162 ∧ 0 ≤ d.w2 12569 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12569 ≤ 2 * (228 / 100 : ℝ) / 12569 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12569 ≤ 2 * (370 / 100 : ℝ) / 12569 := by
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
    (completeRAData (tableEnvelope C) 12569 162).locationBound 12569 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12569 162).energyBound 12569 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12569 162) (d.f1 12569 162) d.f2 ≤
      32 * (((4703052263 / 1000000000000000000) : ℝ) + (1569017939 / 1000000000000000000) + (5892407 / 15625000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12569 162) (d.w1 12569 162)
      (d.w2 12569 162) ≤
      32 * (((29548769 / 1562500000000000000) : ℝ) + (1345496639 / 100000000000000000000) + (122902727 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12569 162) (d.f1 12569 162) d.f2 ≤
      ((4703052263 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4703052263 / 1000000000000000000)) * ((1569017939 / 1000000000000000000)) * (126 / 100) +
      2 * (((1569017939 / 1000000000000000000)) ^ 2 + 2 * ((4703052263 / 1000000000000000000)) * ((5892407 / 15625000000000000))) +
      6 * ((1569017939 / 1000000000000000000)) * ((5892407 / 15625000000000000)) * (126 / 100) + 8 * ((5892407 / 15625000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12569 162) (d.f1 12569 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12569 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12569 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12569 162) (d.f1 12569 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12569 162) (d.w1 12569 162) (d.w2 12569 162)
  have hwexpr0 : 0 ≤ d.w0 12569 162 + d.w1 12569 162 * √(π / 2) +
      2 * d.w2 12569 162 + energyR16 12569 *
      radiusPolynomialRoot16 (d.w0 12569 162) (d.w1 12569 162) (d.w2 12569 162) := by
    positivity
  constructor
  · change (12569 : ℝ) ^ 8 * (mA 12569 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12569 162) (d.f1 12569 162) d.f2 + locationR16 12569 *
        radiusPolynomialRoot16 (d.f0 12569 162) (d.f1 12569 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12569 : ℝ) ^ 8 * (mA 12569 : ℝ) ^ 8 *
        ((((4703052263 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4703052263 / 1000000000000000000)) * ((1569017939 / 1000000000000000000)) * (126 / 100) +
          2 * (((1569017939 / 1000000000000000000)) ^ 2 + 2 * ((4703052263 / 1000000000000000000)) * ((5892407 / 15625000000000000))) +
          6 * ((1569017939 / 1000000000000000000)) * ((5892407 / 15625000000000000)) * (126 / 100) + 8 * ((5892407 / 15625000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12569) *
          (32 * (((4703052263 / 1000000000000000000) : ℝ) + (1569017939 / 1000000000000000000) + (5892407 / 15625000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12569 : ℝ) ^ 16 *
      (d.w0 12569 162 + d.w1 12569 162 * √(π / 2) + 2 * d.w2 12569 162 +
        energyR16 12569 * radiusPolynomialRoot16 (d.w0 12569 162) (d.w1 12569 162)
          (d.w2 12569 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12569 : ℝ) ^ 16 *
        (((29548769 / 1562500000000000000) : ℝ) + ((1345496639 / 100000000000000000000)) * (126 / 100) + 2 * ((122902727 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12569) *
          (32 * (((29548769 / 1562500000000000000) : ℝ) + (1345496639 / 100000000000000000000) + (122902727 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12569

/-! A coarse bound on the actual paper statistics constant at dimension 12570. -/
namespace BstLean.Part266.Row12570
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12568 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12568 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12568 128 ≤ (12822 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12822 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12570) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12570 : ℕ))
    (by norm_num : (12570 : ℕ) ≤ 16384)
  have ht : paperTail256 12570 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12570 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12570 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12570 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12570 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12570 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12568 128 * √(2 / (12570 : ℝ)) *
      (√(12570 : ℝ) + paperT0 12570 + paperTail256 12570) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12570 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12570 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12570 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12568 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12568 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12570 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12570

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12570
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12570 (61 / 100) 162 (17 / (100 * 12570)) (26 / (10 * 12570)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12570 (61 / 100) 162 (17 / (100 * 12570)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (98297639 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (62560153 / 40000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5558370733 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12570 / 12570 * (61 / 100)) ^ 4 * inverseRadius8 (12570 - 1) /
            envelopeGap 12570 (61 / 100) 162 (17 / (100 * 12570)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12570

namespace BstLean.Part266.Row12570
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12570 162 ≤ (4702115813 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12570 162 ≤ (1568705633 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (75407803 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12570 162 ≤ (59083427 / 3125000000000000000)
  w1 : (tableEnvelope C).w1 12570 162 ≤ (67258771 / 5000000000000000000)
  w2 : (tableEnvelope C).w2 12570 162 ≤ (24574679 / 5000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (98297639 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (98297639 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (62560153 / 40000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5558370733 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((735507 / 200000000) : ℝ) ≤ √(17 / (100 * 12570) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12570) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (277119163 / 125000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39547488227 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12570) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12570) ≤ (56253523 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12570) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12570 * (162 : ℝ) ^ 2 + 26 / (10 * 12570) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12570) : ℝ)) (tA 12570 * 162 ^ 2 + 26 / (10 * 12570)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((735507 / 200000000))) * ((98297639 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((735507 / 200000000)) ^ 3) * ((62560153 / 40000000000000000000000))) + ((5558370733 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((735507 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12570) : ℝ)) d.D d.V d.P (√(tA 12570) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((735507 / 200000000)) ^ 2 * (((277119163 / 125000000000000)) * ((39547488227 / 1000000000000000000)))) + ((5558370733 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12570) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((735507 / 200000000)) * ((98297639 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12570) : ℝ)) (tA 12570 * 162 ^ 2 + 26 / (10 * 12570)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((98297639 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((735507 / 200000000)) ^ 2) * ((62560153 / 40000000000000000000000)) + ((5558370733 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12570) : ℝ)) (√(26 / (10 * 12570) : ℝ)) d.D d.V d.P (√(tA 12570) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((735507 / 200000000)) * (((277119163 / 125000000000000)) * ((39547488227 / 1000000000000000000))) + ((5558370733 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12570) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((98297639 / 20000000000000000000) : ℝ) + ((5558370733 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12570

namespace BstLean.Part266.Row12570
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12570 162 ∧
    0 ≤ (tableEnvelope C).f1 12570 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12570 162 ∧
    0 ≤ (tableEnvelope C).w1 12570 162 ∧ 0 ≤ (tableEnvelope C).w2 12570 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12570 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12570 162 ∧ 0 ≤ d.f1 12570 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12570 162 ∧ 0 ≤ d.w1 12570 162 ∧ 0 ≤ d.w2 12570 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12570 ≤ 2 * (228 / 100 : ℝ) / 12570 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12570 ≤ 2 * (370 / 100 : ℝ) / 12570 := by
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
    (completeRAData (tableEnvelope C) 12570 162).locationBound 12570 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12570 162).energyBound 12570 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12570 162) (d.f1 12570 162) d.f2 ≤
      32 * (((4702115813 / 1000000000000000000) : ℝ) + (1568705633 / 1000000000000000000) + (75407803 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12570 162) (d.w1 12570 162)
      (d.w2 12570 162) ≤
      32 * (((59083427 / 3125000000000000000) : ℝ) + (67258771 / 5000000000000000000) + (24574679 / 5000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12570 162) (d.f1 12570 162) d.f2 ≤
      ((4702115813 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4702115813 / 1000000000000000000)) * ((1568705633 / 1000000000000000000)) * (126 / 100) +
      2 * (((1568705633 / 1000000000000000000)) ^ 2 + 2 * ((4702115813 / 1000000000000000000)) * ((75407803 / 200000000000000000))) +
      6 * ((1568705633 / 1000000000000000000)) * ((75407803 / 200000000000000000)) * (126 / 100) + 8 * ((75407803 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12570 162) (d.f1 12570 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12570 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12570 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12570 162) (d.f1 12570 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12570 162) (d.w1 12570 162) (d.w2 12570 162)
  have hwexpr0 : 0 ≤ d.w0 12570 162 + d.w1 12570 162 * √(π / 2) +
      2 * d.w2 12570 162 + energyR16 12570 *
      radiusPolynomialRoot16 (d.w0 12570 162) (d.w1 12570 162) (d.w2 12570 162) := by
    positivity
  constructor
  · change (12570 : ℝ) ^ 8 * (mA 12570 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12570 162) (d.f1 12570 162) d.f2 + locationR16 12570 *
        radiusPolynomialRoot16 (d.f0 12570 162) (d.f1 12570 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12570 : ℝ) ^ 8 * (mA 12570 : ℝ) ^ 8 *
        ((((4702115813 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4702115813 / 1000000000000000000)) * ((1568705633 / 1000000000000000000)) * (126 / 100) +
          2 * (((1568705633 / 1000000000000000000)) ^ 2 + 2 * ((4702115813 / 1000000000000000000)) * ((75407803 / 200000000000000000))) +
          6 * ((1568705633 / 1000000000000000000)) * ((75407803 / 200000000000000000)) * (126 / 100) + 8 * ((75407803 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12570) *
          (32 * (((4702115813 / 1000000000000000000) : ℝ) + (1568705633 / 1000000000000000000) + (75407803 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12570 : ℝ) ^ 16 *
      (d.w0 12570 162 + d.w1 12570 162 * √(π / 2) + 2 * d.w2 12570 162 +
        energyR16 12570 * radiusPolynomialRoot16 (d.w0 12570 162) (d.w1 12570 162)
          (d.w2 12570 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12570 : ℝ) ^ 16 *
        (((59083427 / 3125000000000000000) : ℝ) + ((67258771 / 5000000000000000000)) * (126 / 100) + 2 * ((24574679 / 5000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12570) *
          (32 * (((59083427 / 3125000000000000000) : ℝ) + (67258771 / 5000000000000000000) + (24574679 / 5000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12570

/-! A coarse bound on the actual paper statistics constant at dimension 12571. -/
namespace BstLean.Part266.Row12571
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12569 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12569 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12569 128 ≤ (12823 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12823 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12571) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12571 : ℕ))
    (by norm_num : (12571 : ℕ) ≤ 16384)
  have ht : paperTail256 12571 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12571 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12571 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12571 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12571 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12571 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12569 128 * √(2 / (12571 : ℝ)) *
      (√(12571 : ℝ) + paperT0 12571 + paperTail256 12571) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12571 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12571 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12571 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12569 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12569 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12571 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12571

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12571
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12571 (61 / 100) 162 (17 / (100 * 12571)) (26 / (10 * 12571)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12571 (61 / 100) 162 (17 / (100 * 12571)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (491370907 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (156350621 / 100000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (555479973 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12571 / 12571 * (61 / 100)) ^ 4 * inverseRadius8 (12571 - 1) /
            envelopeGap 12571 (61 / 100) 162 (17 / (100 * 12571)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12571

namespace BstLean.Part266.Row12571
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12571 162 ≤ (2350591689 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12571 162 ≤ (784197141 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (376964107 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12571 162 ≤ (1890219031 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12571 162 ≤ (53794187 / 4000000000000000000)
  w2 : (tableEnvelope C).w2 12571 162 ≤ (15355509 / 3125000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (491370907 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (491370907 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (156350621 / 100000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (555479973 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((919347 / 250000000) : ℝ) ≤ √(17 / (100 * 12571) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12571) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2216688763 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19770598183 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12571) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12571) ≤ (7031131 / 62500000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12571) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12571 * (162 : ℝ) ^ 2 + 26 / (10 * 12571) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12571) : ℝ)) (tA 12571 * 162 ^ 2 + 26 / (10 * 12571)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((919347 / 250000000))) * ((491370907 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((919347 / 250000000)) ^ 3) * ((156350621 / 100000000000000000000000))) + ((555479973 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((919347 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12571) : ℝ)) d.D d.V d.P (√(tA 12571) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((919347 / 250000000)) ^ 2 * (((2216688763 / 1000000000000000)) * ((19770598183 / 500000000000000000)))) + ((555479973 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12571) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((919347 / 250000000)) * ((491370907 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12571) : ℝ)) (tA 12571 * 162 ^ 2 + 26 / (10 * 12571)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((491370907 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((919347 / 250000000)) ^ 2) * ((156350621 / 100000000000000000000000)) + ((555479973 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12571) : ℝ)) (√(26 / (10 * 12571) : ℝ)) d.D d.V d.P (√(tA 12571) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((919347 / 250000000)) * (((2216688763 / 1000000000000000)) * ((19770598183 / 500000000000000000))) + ((555479973 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12571) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((491370907 / 100000000000000000000) : ℝ) + ((555479973 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12571

namespace BstLean.Part266.Row12571
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12571 162 ∧
    0 ≤ (tableEnvelope C).f1 12571 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12571 162 ∧
    0 ≤ (tableEnvelope C).w1 12571 162 ∧ 0 ≤ (tableEnvelope C).w2 12571 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12571 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12571 162 ∧ 0 ≤ d.f1 12571 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12571 162 ∧ 0 ≤ d.w1 12571 162 ∧ 0 ≤ d.w2 12571 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12571 ≤ 2 * (228 / 100 : ℝ) / 12571 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12571 ≤ 2 * (370 / 100 : ℝ) / 12571 := by
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
    (completeRAData (tableEnvelope C) 12571 162).locationBound 12571 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12571 162).energyBound 12571 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12571 162) (d.f1 12571 162) d.f2 ≤
      32 * (((2350591689 / 500000000000000000) : ℝ) + (784197141 / 500000000000000000) + (376964107 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12571 162) (d.w1 12571 162)
      (d.w2 12571 162) ≤
      32 * (((1890219031 / 100000000000000000000) : ℝ) + (53794187 / 4000000000000000000) + (15355509 / 3125000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12571 162) (d.f1 12571 162) d.f2 ≤
      ((2350591689 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2350591689 / 500000000000000000)) * ((784197141 / 500000000000000000)) * (126 / 100) +
      2 * (((784197141 / 500000000000000000)) ^ 2 + 2 * ((2350591689 / 500000000000000000)) * ((376964107 / 1000000000000000000))) +
      6 * ((784197141 / 500000000000000000)) * ((376964107 / 1000000000000000000)) * (126 / 100) + 8 * ((376964107 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12571 162) (d.f1 12571 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12571 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12571 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12571 162) (d.f1 12571 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12571 162) (d.w1 12571 162) (d.w2 12571 162)
  have hwexpr0 : 0 ≤ d.w0 12571 162 + d.w1 12571 162 * √(π / 2) +
      2 * d.w2 12571 162 + energyR16 12571 *
      radiusPolynomialRoot16 (d.w0 12571 162) (d.w1 12571 162) (d.w2 12571 162) := by
    positivity
  constructor
  · change (12571 : ℝ) ^ 8 * (mA 12571 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12571 162) (d.f1 12571 162) d.f2 + locationR16 12571 *
        radiusPolynomialRoot16 (d.f0 12571 162) (d.f1 12571 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12571 : ℝ) ^ 8 * (mA 12571 : ℝ) ^ 8 *
        ((((2350591689 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2350591689 / 500000000000000000)) * ((784197141 / 500000000000000000)) * (126 / 100) +
          2 * (((784197141 / 500000000000000000)) ^ 2 + 2 * ((2350591689 / 500000000000000000)) * ((376964107 / 1000000000000000000))) +
          6 * ((784197141 / 500000000000000000)) * ((376964107 / 1000000000000000000)) * (126 / 100) + 8 * ((376964107 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12571) *
          (32 * (((2350591689 / 500000000000000000) : ℝ) + (784197141 / 500000000000000000) + (376964107 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12571 : ℝ) ^ 16 *
      (d.w0 12571 162 + d.w1 12571 162 * √(π / 2) + 2 * d.w2 12571 162 +
        energyR16 12571 * radiusPolynomialRoot16 (d.w0 12571 162) (d.w1 12571 162)
          (d.w2 12571 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12571 : ℝ) ^ 16 *
        (((1890219031 / 100000000000000000000) : ℝ) + ((53794187 / 4000000000000000000)) * (126 / 100) + 2 * ((15355509 / 3125000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12571) *
          (32 * (((1890219031 / 100000000000000000000) : ℝ) + (53794187 / 4000000000000000000) + (15355509 / 3125000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12571

/-! A coarse bound on the actual paper statistics constant at dimension 12572. -/
namespace BstLean.Part266.Row12572
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12570 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12570 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12570 128 ≤ (12824 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12824 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12572) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12572 : ℕ))
    (by norm_num : (12572 : ℕ) ≤ 16384)
  have ht : paperTail256 12572 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12572 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12572 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12572 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12572 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12572 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12570 128 * √(2 / (12572 : ℝ)) *
      (√(12572 : ℝ) + paperT0 12572 + paperTail256 12572) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12572 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12572 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12572 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12570 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12570 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12572 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12572

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12572
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12572 (61 / 100) 162 (17 / (100 * 12572)) (26 / (10 * 12572)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12572 (61 / 100) 162 (17 / (100 * 12572)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (61406707 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1563008793 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5551231311 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12572 / 12572 * (61 / 100)) ^ 4 * inverseRadius8 (12572 - 1) /
            envelopeGap 12572 (61 / 100) 162 (17 / (100 * 12572)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12572

namespace BstLean.Part266.Row12572
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12572 162 ≤ (2350123789 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12572 162 ≤ (1568082179 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (376889119 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12572 162 ≤ (118110487 / 6250000000000000000)
  w1 : (tableEnvelope C).w1 12572 162 ≤ (168066709 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 12572 162 ≤ (245629517 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (61406707 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (61406707 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1563008793 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5551231311 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1838621 / 500000000) : ℝ) ≤ √(17 / (100 * 12572) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12572) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1108212137 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4941863251 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12572) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12572) ≤ (28122287 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12572) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12572 * (162 : ℝ) ^ 2 + 26 / (10 * 12572) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12572) : ℝ)) (tA 12572 * 162 ^ 2 + 26 / (10 * 12572)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1838621 / 500000000))) * ((61406707 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1838621 / 500000000)) ^ 3) * ((1563008793 / 1000000000000000000000000))) + ((5551231311 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1838621 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12572) : ℝ)) d.D d.V d.P (√(tA 12572) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1838621 / 500000000)) ^ 2 * (((1108212137 / 500000000000000)) * ((4941863251 / 125000000000000000)))) + ((5551231311 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12572) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1838621 / 500000000)) * ((61406707 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12572) : ℝ)) (tA 12572 * 162 ^ 2 + 26 / (10 * 12572)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((61406707 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1838621 / 500000000)) ^ 2) * ((1563008793 / 1000000000000000000000000)) + ((5551231311 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12572) : ℝ)) (√(26 / (10 * 12572) : ℝ)) d.D d.V d.P (√(tA 12572) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1838621 / 500000000)) * (((1108212137 / 500000000000000)) * ((4941863251 / 125000000000000000))) + ((5551231311 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12572) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((61406707 / 12500000000000000000) : ℝ) + ((5551231311 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12572

namespace BstLean.Part266.Row12572
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12572 162 ∧
    0 ≤ (tableEnvelope C).f1 12572 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12572 162 ∧
    0 ≤ (tableEnvelope C).w1 12572 162 ∧ 0 ≤ (tableEnvelope C).w2 12572 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12572 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12572 162 ∧ 0 ≤ d.f1 12572 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12572 162 ∧ 0 ≤ d.w1 12572 162 ∧ 0 ≤ d.w2 12572 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12572 ≤ 2 * (228 / 100 : ℝ) / 12572 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12572 ≤ 2 * (370 / 100 : ℝ) / 12572 := by
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
    (completeRAData (tableEnvelope C) 12572 162).locationBound 12572 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12572 162).energyBound 12572 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12572 162) (d.f1 12572 162) d.f2 ≤
      32 * (((2350123789 / 500000000000000000) : ℝ) + (1568082179 / 1000000000000000000) + (376889119 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12572 162) (d.w1 12572 162)
      (d.w2 12572 162) ≤
      32 * (((118110487 / 6250000000000000000) : ℝ) + (168066709 / 12500000000000000000) + (245629517 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12572 162) (d.f1 12572 162) d.f2 ≤
      ((2350123789 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2350123789 / 500000000000000000)) * ((1568082179 / 1000000000000000000)) * (126 / 100) +
      2 * (((1568082179 / 1000000000000000000)) ^ 2 + 2 * ((2350123789 / 500000000000000000)) * ((376889119 / 1000000000000000000))) +
      6 * ((1568082179 / 1000000000000000000)) * ((376889119 / 1000000000000000000)) * (126 / 100) + 8 * ((376889119 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12572 162) (d.f1 12572 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12572 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12572 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12572 162) (d.f1 12572 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12572 162) (d.w1 12572 162) (d.w2 12572 162)
  have hwexpr0 : 0 ≤ d.w0 12572 162 + d.w1 12572 162 * √(π / 2) +
      2 * d.w2 12572 162 + energyR16 12572 *
      radiusPolynomialRoot16 (d.w0 12572 162) (d.w1 12572 162) (d.w2 12572 162) := by
    positivity
  constructor
  · change (12572 : ℝ) ^ 8 * (mA 12572 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12572 162) (d.f1 12572 162) d.f2 + locationR16 12572 *
        radiusPolynomialRoot16 (d.f0 12572 162) (d.f1 12572 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12572 : ℝ) ^ 8 * (mA 12572 : ℝ) ^ 8 *
        ((((2350123789 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2350123789 / 500000000000000000)) * ((1568082179 / 1000000000000000000)) * (126 / 100) +
          2 * (((1568082179 / 1000000000000000000)) ^ 2 + 2 * ((2350123789 / 500000000000000000)) * ((376889119 / 1000000000000000000))) +
          6 * ((1568082179 / 1000000000000000000)) * ((376889119 / 1000000000000000000)) * (126 / 100) + 8 * ((376889119 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12572) *
          (32 * (((2350123789 / 500000000000000000) : ℝ) + (1568082179 / 1000000000000000000) + (376889119 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12572 : ℝ) ^ 16 *
      (d.w0 12572 162 + d.w1 12572 162 * √(π / 2) + 2 * d.w2 12572 162 +
        energyR16 12572 * radiusPolynomialRoot16 (d.w0 12572 162) (d.w1 12572 162)
          (d.w2 12572 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12572 : ℝ) ^ 16 *
        (((118110487 / 6250000000000000000) : ℝ) + ((168066709 / 12500000000000000000)) * (126 / 100) + 2 * ((245629517 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12572) *
          (32 * (((118110487 / 6250000000000000000) : ℝ) + (168066709 / 12500000000000000000) + (245629517 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12572

/-! A coarse bound on the actual paper statistics constant at dimension 12573. -/
namespace BstLean.Part266.Row12573
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12571 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12571 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12571 128 ≤ (12825 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12825 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12573) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12573 : ℕ))
    (by norm_num : (12573 : ℕ) ≤ 16384)
  have ht : paperTail256 12573 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12573 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12573 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12573 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12573 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12573 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12571 128 * √(2 / (12573 : ℝ)) *
      (√(12573 : ℝ) + paperT0 12573 + paperTail256 12573) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12573 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12573 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12573 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12571 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12571 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12573 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12573

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12573
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12573 (61 / 100) 162 (17 / (100 * 12573)) (26 / (10 * 12573)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12573 (61 / 100) 162 (17 / (100 * 12573)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (491136443 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1562511573 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5547665473 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12573 / 12573 * (61 / 100)) ^ 4 * inverseRadius8 (12573 - 1) /
            envelopeGap 12573 (61 / 100) 162 (17 / (100 * 12573)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12573

namespace BstLean.Part266.Row12573
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12573 162 ≤ (46993121 / 10000000000000000)
  f1 : (tableEnvelope C).f1 12573 162 ≤ (783885089 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (188407077 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12573 162 ≤ (1889316711 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12573 162 ≤ (1344212779 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12573 162 ≤ (491141817 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (491136443 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (491136443 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1562511573 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5547665473 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((459637 / 125000000) : ℝ) ≤ √(17 / (100 * 12573) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12573) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2216159839 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1976430857 / 50000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12573) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12573) ≤ (112480201 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12573) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12573 * (162 : ℝ) ^ 2 + 26 / (10 * 12573) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12573) : ℝ)) (tA 12573 * 162 ^ 2 + 26 / (10 * 12573)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((459637 / 125000000))) * ((491136443 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((459637 / 125000000)) ^ 3) * ((1562511573 / 1000000000000000000000000))) + ((5547665473 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((459637 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12573) : ℝ)) d.D d.V d.P (√(tA 12573) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((459637 / 125000000)) ^ 2 * (((2216159839 / 1000000000000000)) * ((1976430857 / 50000000000000000)))) + ((5547665473 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12573) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((459637 / 125000000)) * ((491136443 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12573) : ℝ)) (tA 12573 * 162 ^ 2 + 26 / (10 * 12573)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((491136443 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((459637 / 125000000)) ^ 2) * ((1562511573 / 1000000000000000000000000)) + ((5547665473 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12573) : ℝ)) (√(26 / (10 * 12573) : ℝ)) d.D d.V d.P (√(tA 12573) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((459637 / 125000000)) * (((2216159839 / 1000000000000000)) * ((1976430857 / 50000000000000000))) + ((5547665473 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12573) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((491136443 / 100000000000000000000) : ℝ) + ((5547665473 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12573

namespace BstLean.Part266.Row12573
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12573 162 ∧
    0 ≤ (tableEnvelope C).f1 12573 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12573 162 ∧
    0 ≤ (tableEnvelope C).w1 12573 162 ∧ 0 ≤ (tableEnvelope C).w2 12573 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12573 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12573 162 ∧ 0 ≤ d.f1 12573 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12573 162 ∧ 0 ≤ d.w1 12573 162 ∧ 0 ≤ d.w2 12573 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12573 ≤ 2 * (228 / 100 : ℝ) / 12573 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12573 ≤ 2 * (370 / 100 : ℝ) / 12573 := by
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
    (completeRAData (tableEnvelope C) 12573 162).locationBound 12573 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12573 162).energyBound 12573 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12573 162) (d.f1 12573 162) d.f2 ≤
      32 * (((46993121 / 10000000000000000) : ℝ) + (783885089 / 500000000000000000) + (188407077 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12573 162) (d.w1 12573 162)
      (d.w2 12573 162) ≤
      32 * (((1889316711 / 100000000000000000000) : ℝ) + (1344212779 / 100000000000000000000) + (491141817 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12573 162) (d.f1 12573 162) d.f2 ≤
      ((46993121 / 10000000000000000) : ℝ) ^ 2 + 2 * ((46993121 / 10000000000000000)) * ((783885089 / 500000000000000000)) * (126 / 100) +
      2 * (((783885089 / 500000000000000000)) ^ 2 + 2 * ((46993121 / 10000000000000000)) * ((188407077 / 500000000000000000))) +
      6 * ((783885089 / 500000000000000000)) * ((188407077 / 500000000000000000)) * (126 / 100) + 8 * ((188407077 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12573 162) (d.f1 12573 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12573 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12573 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12573 162) (d.f1 12573 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12573 162) (d.w1 12573 162) (d.w2 12573 162)
  have hwexpr0 : 0 ≤ d.w0 12573 162 + d.w1 12573 162 * √(π / 2) +
      2 * d.w2 12573 162 + energyR16 12573 *
      radiusPolynomialRoot16 (d.w0 12573 162) (d.w1 12573 162) (d.w2 12573 162) := by
    positivity
  constructor
  · change (12573 : ℝ) ^ 8 * (mA 12573 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12573 162) (d.f1 12573 162) d.f2 + locationR16 12573 *
        radiusPolynomialRoot16 (d.f0 12573 162) (d.f1 12573 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12573 : ℝ) ^ 8 * (mA 12573 : ℝ) ^ 8 *
        ((((46993121 / 10000000000000000) : ℝ) ^ 2 + 2 * ((46993121 / 10000000000000000)) * ((783885089 / 500000000000000000)) * (126 / 100) +
          2 * (((783885089 / 500000000000000000)) ^ 2 + 2 * ((46993121 / 10000000000000000)) * ((188407077 / 500000000000000000))) +
          6 * ((783885089 / 500000000000000000)) * ((188407077 / 500000000000000000)) * (126 / 100) + 8 * ((188407077 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12573) *
          (32 * (((46993121 / 10000000000000000) : ℝ) + (783885089 / 500000000000000000) + (188407077 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12573 : ℝ) ^ 16 *
      (d.w0 12573 162 + d.w1 12573 162 * √(π / 2) + 2 * d.w2 12573 162 +
        energyR16 12573 * radiusPolynomialRoot16 (d.w0 12573 162) (d.w1 12573 162)
          (d.w2 12573 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12573 : ℝ) ^ 16 *
        (((1889316711 / 100000000000000000000) : ℝ) + ((1344212779 / 100000000000000000000)) * (126 / 100) + 2 * ((491141817 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12573) *
          (32 * (((1889316711 / 100000000000000000000) : ℝ) + (1344212779 / 100000000000000000000) + (491141817 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12573

/-! A coarse bound on the actual paper statistics constant at dimension 12574. -/
namespace BstLean.Part266.Row12574
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12572 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12572 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12572 128 ≤ (12826 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12826 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12574) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12574 : ℕ))
    (by norm_num : (12574 : ℕ) ≤ 16384)
  have ht : paperTail256 12574 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12574 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12574 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12574 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12574 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12574 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12572 128 * √(2 / (12574 : ℝ)) *
      (√(12574 : ℝ) + paperT0 12574 + paperTail256 12574) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12574 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12574 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12574 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12572 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12572 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12574 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12574

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12574
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12574 (61 / 100) 162 (17 / (100 * 12574)) (26 / (10 * 12574)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12574 (61 / 100) 162 (17 / (100 * 12574)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (491019267 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (195251819 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1108820443 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12574 / 12574 * (61 / 100)) ^ 4 * inverseRadius8 (12574 - 1) /
            envelopeGap 12574 (61 / 100) 162 (17 / (100 * 12574)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12574

namespace BstLean.Part266.Row12574
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12574 162 ≤ (4698376951 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12574 162 ≤ (39186457 / 25000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (94184803 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12574 162 ≤ (1888865787 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12574 162 ≤ (671945997 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12574 162 ≤ (245512319 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (491019267 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (491019267 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (195251819 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1108820443 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((73539 / 20000000) : ℝ) ≤ √(17 / (100 * 12574) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12574) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (69246733 / 31250000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3952232979 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12574) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12574) ≤ (14058907 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12574) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12574 * (162 : ℝ) ^ 2 + 26 / (10 * 12574) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12574) : ℝ)) (tA 12574 * 162 ^ 2 + 26 / (10 * 12574)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((73539 / 20000000))) * ((491019267 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((73539 / 20000000)) ^ 3) * ((195251819 / 125000000000000000000000))) + ((1108820443 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((73539 / 20000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12574) : ℝ)) d.D d.V d.P (√(tA 12574) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((73539 / 20000000)) ^ 2 * (((69246733 / 31250000000000)) * ((3952232979 / 100000000000000000)))) + ((1108820443 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12574) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((73539 / 20000000)) * ((491019267 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12574) : ℝ)) (tA 12574 * 162 ^ 2 + 26 / (10 * 12574)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((491019267 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((73539 / 20000000)) ^ 2) * ((195251819 / 125000000000000000000000)) + ((1108820443 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12574) : ℝ)) (√(26 / (10 * 12574) : ℝ)) d.D d.V d.P (√(tA 12574) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((73539 / 20000000)) * (((69246733 / 31250000000000)) * ((3952232979 / 100000000000000000))) + ((1108820443 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12574) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((491019267 / 100000000000000000000) : ℝ) + ((1108820443 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12574

namespace BstLean.Part266.Row12574
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12574 162 ∧
    0 ≤ (tableEnvelope C).f1 12574 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12574 162 ∧
    0 ≤ (tableEnvelope C).w1 12574 162 ∧ 0 ≤ (tableEnvelope C).w2 12574 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12574 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12574 162 ∧ 0 ≤ d.f1 12574 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12574 162 ∧ 0 ≤ d.w1 12574 162 ∧ 0 ≤ d.w2 12574 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12574 ≤ 2 * (228 / 100 : ℝ) / 12574 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12574 ≤ 2 * (370 / 100 : ℝ) / 12574 := by
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
    (completeRAData (tableEnvelope C) 12574 162).locationBound 12574 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12574 162).energyBound 12574 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12574 162) (d.f1 12574 162) d.f2 ≤
      32 * (((4698376951 / 1000000000000000000) : ℝ) + (39186457 / 25000000000000000) + (94184803 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12574 162) (d.w1 12574 162)
      (d.w2 12574 162) ≤
      32 * (((1888865787 / 100000000000000000000) : ℝ) + (671945997 / 50000000000000000000) + (245512319 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12574 162) (d.f1 12574 162) d.f2 ≤
      ((4698376951 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4698376951 / 1000000000000000000)) * ((39186457 / 25000000000000000)) * (126 / 100) +
      2 * (((39186457 / 25000000000000000)) ^ 2 + 2 * ((4698376951 / 1000000000000000000)) * ((94184803 / 250000000000000000))) +
      6 * ((39186457 / 25000000000000000)) * ((94184803 / 250000000000000000)) * (126 / 100) + 8 * ((94184803 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12574 162) (d.f1 12574 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12574 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12574 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12574 162) (d.f1 12574 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12574 162) (d.w1 12574 162) (d.w2 12574 162)
  have hwexpr0 : 0 ≤ d.w0 12574 162 + d.w1 12574 162 * √(π / 2) +
      2 * d.w2 12574 162 + energyR16 12574 *
      radiusPolynomialRoot16 (d.w0 12574 162) (d.w1 12574 162) (d.w2 12574 162) := by
    positivity
  constructor
  · change (12574 : ℝ) ^ 8 * (mA 12574 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12574 162) (d.f1 12574 162) d.f2 + locationR16 12574 *
        radiusPolynomialRoot16 (d.f0 12574 162) (d.f1 12574 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12574 : ℝ) ^ 8 * (mA 12574 : ℝ) ^ 8 *
        ((((4698376951 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4698376951 / 1000000000000000000)) * ((39186457 / 25000000000000000)) * (126 / 100) +
          2 * (((39186457 / 25000000000000000)) ^ 2 + 2 * ((4698376951 / 1000000000000000000)) * ((94184803 / 250000000000000000))) +
          6 * ((39186457 / 25000000000000000)) * ((94184803 / 250000000000000000)) * (126 / 100) + 8 * ((94184803 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12574) *
          (32 * (((4698376951 / 1000000000000000000) : ℝ) + (39186457 / 25000000000000000) + (94184803 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12574 : ℝ) ^ 16 *
      (d.w0 12574 162 + d.w1 12574 162 * √(π / 2) + 2 * d.w2 12574 162 +
        energyR16 12574 * radiusPolynomialRoot16 (d.w0 12574 162) (d.w1 12574 162)
          (d.w2 12574 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12574 : ℝ) ^ 16 *
        (((1888865787 / 100000000000000000000) : ℝ) + ((671945997 / 50000000000000000000)) * (126 / 100) + 2 * ((245512319 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12574) *
          (32 * (((1888865787 / 100000000000000000000) : ℝ) + (671945997 / 50000000000000000000) + (245512319 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12574
