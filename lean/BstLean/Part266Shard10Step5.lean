import BstLean.Part266Shard10Step4


/-! A coarse bound on the actual paper statistics constant at dimension 12600. -/
namespace BstLean.Part266.Row12600
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12598 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12598 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12598 128 ≤ (12852 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12852 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12600) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12600 : ℕ))
    (by norm_num : (12600 : ℕ) ≤ 16384)
  have ht : paperTail256 12600 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12600 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12600 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12600 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12600 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12600 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12598 128 * √(2 / (12600 : ℝ)) *
      (√(12600 : ℝ) + paperT0 12600 + paperTail256 12600) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12600 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12600 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12600 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12598 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12598 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12600 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12600

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12600
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12600 (61 / 100) 162 (17 / (100 * 12600)) (26 / (10 * 12600)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12600 (61 / 100) 162 (17 / (100 * 12600)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (121996433 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (387290269 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5452356073 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12600 / 12600 * (61 / 100)) ^ 4 * inverseRadius8 (12600 - 1) /
            envelopeGap 12600 (61 / 100) 162 (17 / (100 * 12600)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12600

namespace BstLean.Part266.Row12600
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12600 162 ≤ (4674176581 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12600 162 ≤ (311876897 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (374798637 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12600 162 ≤ (375439313 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12600 162 ≤ (667794751 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12600 162 ≤ (243995507 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (121996433 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (121996433 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (387290269 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5452356073 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1836577 / 500000000) : ℝ) ≤ √(17 / (100 * 12600) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12600) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (220903991 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39359383583 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12600) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12600) ≤ (28059793 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12600) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12600 * (162 : ℝ) ^ 2 + 26 / (10 * 12600) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12600) : ℝ)) (tA 12600 * 162 ^ 2 + 26 / (10 * 12600)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1836577 / 500000000))) * ((121996433 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1836577 / 500000000)) ^ 3) * ((387290269 / 250000000000000000000000))) + ((5452356073 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1836577 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12600) : ℝ)) d.D d.V d.P (√(tA 12600) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1836577 / 500000000)) ^ 2 * (((220903991 / 100000000000000)) * ((39359383583 / 1000000000000000000)))) + ((5452356073 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12600) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1836577 / 500000000)) * ((121996433 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12600) : ℝ)) (tA 12600 * 162 ^ 2 + 26 / (10 * 12600)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((121996433 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1836577 / 500000000)) ^ 2) * ((387290269 / 250000000000000000000000)) + ((5452356073 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12600) : ℝ)) (√(26 / (10 * 12600) : ℝ)) d.D d.V d.P (√(tA 12600) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1836577 / 500000000)) * (((220903991 / 100000000000000)) * ((39359383583 / 1000000000000000000))) + ((5452356073 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12600) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((121996433 / 25000000000000000000) : ℝ) + ((5452356073 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12600

namespace BstLean.Part266.Row12600
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12600 162 ∧
    0 ≤ (tableEnvelope C).f1 12600 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12600 162 ∧
    0 ≤ (tableEnvelope C).w1 12600 162 ∧ 0 ≤ (tableEnvelope C).w2 12600 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12600 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12600 162 ∧ 0 ≤ d.f1 12600 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12600 162 ∧ 0 ≤ d.w1 12600 162 ∧ 0 ≤ d.w2 12600 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12600 ≤ 2 * (228 / 100 : ℝ) / 12600 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12600 ≤ 2 * (370 / 100 : ℝ) / 12600 := by
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
    (completeRAData (tableEnvelope C) 12600 162).locationBound 12600 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12600 162).energyBound 12600 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12600 162) (d.f1 12600 162) d.f2 ≤
      32 * (((4674176581 / 1000000000000000000) : ℝ) + (311876897 / 200000000000000000) + (374798637 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12600 162) (d.w1 12600 162)
      (d.w2 12600 162) ≤
      32 * (((375439313 / 20000000000000000000) : ℝ) + (667794751 / 50000000000000000000) + (243995507 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12600 162) (d.f1 12600 162) d.f2 ≤
      ((4674176581 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4674176581 / 1000000000000000000)) * ((311876897 / 200000000000000000)) * (126 / 100) +
      2 * (((311876897 / 200000000000000000)) ^ 2 + 2 * ((4674176581 / 1000000000000000000)) * ((374798637 / 1000000000000000000))) +
      6 * ((311876897 / 200000000000000000)) * ((374798637 / 1000000000000000000)) * (126 / 100) + 8 * ((374798637 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12600 162) (d.f1 12600 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12600 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12600 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12600 162) (d.f1 12600 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12600 162) (d.w1 12600 162) (d.w2 12600 162)
  have hwexpr0 : 0 ≤ d.w0 12600 162 + d.w1 12600 162 * √(π / 2) +
      2 * d.w2 12600 162 + energyR16 12600 *
      radiusPolynomialRoot16 (d.w0 12600 162) (d.w1 12600 162) (d.w2 12600 162) := by
    positivity
  constructor
  · change (12600 : ℝ) ^ 8 * (mA 12600 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12600 162) (d.f1 12600 162) d.f2 + locationR16 12600 *
        radiusPolynomialRoot16 (d.f0 12600 162) (d.f1 12600 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12600 : ℝ) ^ 8 * (mA 12600 : ℝ) ^ 8 *
        ((((4674176581 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4674176581 / 1000000000000000000)) * ((311876897 / 200000000000000000)) * (126 / 100) +
          2 * (((311876897 / 200000000000000000)) ^ 2 + 2 * ((4674176581 / 1000000000000000000)) * ((374798637 / 1000000000000000000))) +
          6 * ((311876897 / 200000000000000000)) * ((374798637 / 1000000000000000000)) * (126 / 100) + 8 * ((374798637 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12600) *
          (32 * (((4674176581 / 1000000000000000000) : ℝ) + (311876897 / 200000000000000000) + (374798637 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12600 : ℝ) ^ 16 *
      (d.w0 12600 162 + d.w1 12600 162 * √(π / 2) + 2 * d.w2 12600 162 +
        energyR16 12600 * radiusPolynomialRoot16 (d.w0 12600 162) (d.w1 12600 162)
          (d.w2 12600 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12600 : ℝ) ^ 16 *
        (((375439313 / 20000000000000000000) : ℝ) + ((667794751 / 50000000000000000000)) * (126 / 100) + 2 * ((243995507 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12600) *
          (32 * (((375439313 / 20000000000000000000) : ℝ) + (667794751 / 50000000000000000000) + (243995507 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12600

/-! A coarse bound on the actual paper statistics constant at dimension 12601. -/
namespace BstLean.Part266.Row12601
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12599 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12599 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12599 128 ≤ (12853 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12853 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12601) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12601 : ℕ))
    (by norm_num : (12601 : ℕ) ≤ 16384)
  have ht : paperTail256 12601 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12601 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12601 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12601 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12601 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12601 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12599 128 * √(2 / (12601 : ℝ)) *
      (√(12601 : ℝ) + paperT0 12601 + paperTail256 12601) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12601 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12601 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12601 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12599 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12599 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12601 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12601

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12601
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12601 (61 / 100) 162 (17 / (100 * 12601)) (26 / (10 * 12601)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12601 (61 / 100) 162 (17 / (100 * 12601)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (487869557 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1548669357 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2724430839 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12601 / 12601 * (61 / 100)) ^ 4 * inverseRadius8 (12601 - 1) /
            envelopeGap 12601 (61 / 100) 162 (17 / (100 * 12601)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12601

namespace BstLean.Part266.Row12601
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12601 162 ≤ (4673250147 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12601 162 ≤ (1559075317 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (374724303 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12601 162 ≤ (234593731 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 12601 162 ≤ (333817907 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12601 162 ≤ (121968709 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (487869557 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (487869557 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1548669357 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2724430839 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((229563 / 62500000) : ℝ) ≤ √(17 / (100 * 12601) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12601) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (110438847 / 50000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39353136559 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12601) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12601) ≤ (22446053 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12601) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12601 * (162 : ℝ) ^ 2 + 26 / (10 * 12601) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12601) : ℝ)) (tA 12601 * 162 ^ 2 + 26 / (10 * 12601)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((229563 / 62500000))) * ((487869557 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((229563 / 62500000)) ^ 3) * ((1548669357 / 1000000000000000000000000))) + ((2724430839 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((229563 / 62500000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12601) : ℝ)) d.D d.V d.P (√(tA 12601) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((229563 / 62500000)) ^ 2 * (((110438847 / 50000000000000)) * ((39353136559 / 1000000000000000000)))) + ((2724430839 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12601) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((229563 / 62500000)) * ((487869557 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12601) : ℝ)) (tA 12601 * 162 ^ 2 + 26 / (10 * 12601)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((487869557 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((229563 / 62500000)) ^ 2) * ((1548669357 / 1000000000000000000000000)) + ((2724430839 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12601) : ℝ)) (√(26 / (10 * 12601) : ℝ)) d.D d.V d.P (√(tA 12601) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((229563 / 62500000)) * (((110438847 / 50000000000000)) * ((39353136559 / 1000000000000000000))) + ((2724430839 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12601) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((487869557 / 100000000000000000000) : ℝ) + ((2724430839 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12601

namespace BstLean.Part266.Row12601
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12601 162 ∧
    0 ≤ (tableEnvelope C).f1 12601 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12601 162 ∧
    0 ≤ (tableEnvelope C).w1 12601 162 ∧ 0 ≤ (tableEnvelope C).w2 12601 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12601 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12601 162 ∧ 0 ≤ d.f1 12601 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12601 162 ∧ 0 ≤ d.w1 12601 162 ∧ 0 ≤ d.w2 12601 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12601 ≤ 2 * (228 / 100 : ℝ) / 12601 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12601 ≤ 2 * (370 / 100 : ℝ) / 12601 := by
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
    (completeRAData (tableEnvelope C) 12601 162).locationBound 12601 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12601 162).energyBound 12601 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12601 162) (d.f1 12601 162) d.f2 ≤
      32 * (((4673250147 / 1000000000000000000) : ℝ) + (1559075317 / 1000000000000000000) + (374724303 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12601 162) (d.w1 12601 162)
      (d.w2 12601 162) ≤
      32 * (((234593731 / 12500000000000000000) : ℝ) + (333817907 / 25000000000000000000) + (121968709 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12601 162) (d.f1 12601 162) d.f2 ≤
      ((4673250147 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4673250147 / 1000000000000000000)) * ((1559075317 / 1000000000000000000)) * (126 / 100) +
      2 * (((1559075317 / 1000000000000000000)) ^ 2 + 2 * ((4673250147 / 1000000000000000000)) * ((374724303 / 1000000000000000000))) +
      6 * ((1559075317 / 1000000000000000000)) * ((374724303 / 1000000000000000000)) * (126 / 100) + 8 * ((374724303 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12601 162) (d.f1 12601 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12601 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12601 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12601 162) (d.f1 12601 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12601 162) (d.w1 12601 162) (d.w2 12601 162)
  have hwexpr0 : 0 ≤ d.w0 12601 162 + d.w1 12601 162 * √(π / 2) +
      2 * d.w2 12601 162 + energyR16 12601 *
      radiusPolynomialRoot16 (d.w0 12601 162) (d.w1 12601 162) (d.w2 12601 162) := by
    positivity
  constructor
  · change (12601 : ℝ) ^ 8 * (mA 12601 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12601 162) (d.f1 12601 162) d.f2 + locationR16 12601 *
        radiusPolynomialRoot16 (d.f0 12601 162) (d.f1 12601 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12601 : ℝ) ^ 8 * (mA 12601 : ℝ) ^ 8 *
        ((((4673250147 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4673250147 / 1000000000000000000)) * ((1559075317 / 1000000000000000000)) * (126 / 100) +
          2 * (((1559075317 / 1000000000000000000)) ^ 2 + 2 * ((4673250147 / 1000000000000000000)) * ((374724303 / 1000000000000000000))) +
          6 * ((1559075317 / 1000000000000000000)) * ((374724303 / 1000000000000000000)) * (126 / 100) + 8 * ((374724303 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12601) *
          (32 * (((4673250147 / 1000000000000000000) : ℝ) + (1559075317 / 1000000000000000000) + (374724303 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12601 : ℝ) ^ 16 *
      (d.w0 12601 162 + d.w1 12601 162 * √(π / 2) + 2 * d.w2 12601 162 +
        energyR16 12601 * radiusPolynomialRoot16 (d.w0 12601 162) (d.w1 12601 162)
          (d.w2 12601 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12601 : ℝ) ^ 16 *
        (((234593731 / 12500000000000000000) : ℝ) + ((333817907 / 25000000000000000000)) * (126 / 100) + 2 * ((121968709 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12601) *
          (32 * (((234593731 / 12500000000000000000) : ℝ) + (333817907 / 25000000000000000000) + (121968709 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12601

/-! A coarse bound on the actual paper statistics constant at dimension 12602. -/
namespace BstLean.Part266.Row12602
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12600 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12600 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12600 128 ≤ (12854 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12854 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12602) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12602 : ℕ))
    (by norm_num : (12602 : ℕ) ≤ 16384)
  have ht : paperTail256 12602 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12602 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12602 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12602 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12602 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12602 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12600 128 * √(2 / (12602 : ℝ)) *
      (√(12602 : ℝ) + paperT0 12602 + paperTail256 12602) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12602 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12602 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12602 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12600 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12600 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12602 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12602

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12602
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12602 (61 / 100) 162 (17 / (100 * 12602)) (26 / (10 * 12602)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12602 (61 / 100) 162 (17 / (100 * 12602)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (487753419 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1548177833 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1089073961 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12602 / 12602 * (61 / 100)) ^ 4 * inverseRadius8 (12602 - 1) /
            envelopeGap 12602 (61 / 100) 162 (17 / (100 * 12602)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12602

namespace BstLean.Part266.Row12602
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12602 162 ≤ (934464807 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12602 162 ≤ (1247013 / 800000000000000)
  f2 : (tableEnvelope C).f2 ≤ (46831249 / 125000000000000000)
  w0 : (tableEnvelope C).w0 12602 162 ≤ (1876303287 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12602 162 ≤ (667476931 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12602 162 ≤ (243879347 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (487753419 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (487753419 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1548177833 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1089073961 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1836431 / 500000000) : ℝ) ≤ √(17 / (100 * 12602) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12602) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (276064253 / 125000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39346891021 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12602) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12602) ≤ (112221359 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12602) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12602 * (162 : ℝ) ^ 2 + 26 / (10 * 12602) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12602) : ℝ)) (tA 12602 * 162 ^ 2 + 26 / (10 * 12602)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1836431 / 500000000))) * ((487753419 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1836431 / 500000000)) ^ 3) * ((1548177833 / 1000000000000000000000000))) + ((1089073961 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1836431 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12602) : ℝ)) d.D d.V d.P (√(tA 12602) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1836431 / 500000000)) ^ 2 * (((276064253 / 125000000000000)) * ((39346891021 / 1000000000000000000)))) + ((1089073961 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12602) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1836431 / 500000000)) * ((487753419 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12602) : ℝ)) (tA 12602 * 162 ^ 2 + 26 / (10 * 12602)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((487753419 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1836431 / 500000000)) ^ 2) * ((1548177833 / 1000000000000000000000000)) + ((1089073961 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12602) : ℝ)) (√(26 / (10 * 12602) : ℝ)) d.D d.V d.P (√(tA 12602) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1836431 / 500000000)) * (((276064253 / 125000000000000)) * ((39346891021 / 1000000000000000000))) + ((1089073961 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12602) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((487753419 / 100000000000000000000) : ℝ) + ((1089073961 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12602

namespace BstLean.Part266.Row12602
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12602 162 ∧
    0 ≤ (tableEnvelope C).f1 12602 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12602 162 ∧
    0 ≤ (tableEnvelope C).w1 12602 162 ∧ 0 ≤ (tableEnvelope C).w2 12602 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12602 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12602 162 ∧ 0 ≤ d.f1 12602 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12602 162 ∧ 0 ≤ d.w1 12602 162 ∧ 0 ≤ d.w2 12602 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12602 ≤ 2 * (228 / 100 : ℝ) / 12602 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12602 ≤ 2 * (370 / 100 : ℝ) / 12602 := by
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
    (completeRAData (tableEnvelope C) 12602 162).locationBound 12602 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12602 162).energyBound 12602 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12602 162) (d.f1 12602 162) d.f2 ≤
      32 * (((934464807 / 200000000000000000) : ℝ) + (1247013 / 800000000000000) + (46831249 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12602 162) (d.w1 12602 162)
      (d.w2 12602 162) ≤
      32 * (((1876303287 / 100000000000000000000) : ℝ) + (667476931 / 50000000000000000000) + (243879347 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12602 162) (d.f1 12602 162) d.f2 ≤
      ((934464807 / 200000000000000000) : ℝ) ^ 2 + 2 * ((934464807 / 200000000000000000)) * ((1247013 / 800000000000000)) * (126 / 100) +
      2 * (((1247013 / 800000000000000)) ^ 2 + 2 * ((934464807 / 200000000000000000)) * ((46831249 / 125000000000000000))) +
      6 * ((1247013 / 800000000000000)) * ((46831249 / 125000000000000000)) * (126 / 100) + 8 * ((46831249 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12602 162) (d.f1 12602 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12602 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12602 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12602 162) (d.f1 12602 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12602 162) (d.w1 12602 162) (d.w2 12602 162)
  have hwexpr0 : 0 ≤ d.w0 12602 162 + d.w1 12602 162 * √(π / 2) +
      2 * d.w2 12602 162 + energyR16 12602 *
      radiusPolynomialRoot16 (d.w0 12602 162) (d.w1 12602 162) (d.w2 12602 162) := by
    positivity
  constructor
  · change (12602 : ℝ) ^ 8 * (mA 12602 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12602 162) (d.f1 12602 162) d.f2 + locationR16 12602 *
        radiusPolynomialRoot16 (d.f0 12602 162) (d.f1 12602 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12602 : ℝ) ^ 8 * (mA 12602 : ℝ) ^ 8 *
        ((((934464807 / 200000000000000000) : ℝ) ^ 2 + 2 * ((934464807 / 200000000000000000)) * ((1247013 / 800000000000000)) * (126 / 100) +
          2 * (((1247013 / 800000000000000)) ^ 2 + 2 * ((934464807 / 200000000000000000)) * ((46831249 / 125000000000000000))) +
          6 * ((1247013 / 800000000000000)) * ((46831249 / 125000000000000000)) * (126 / 100) + 8 * ((46831249 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12602) *
          (32 * (((934464807 / 200000000000000000) : ℝ) + (1247013 / 800000000000000) + (46831249 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12602 : ℝ) ^ 16 *
      (d.w0 12602 162 + d.w1 12602 162 * √(π / 2) + 2 * d.w2 12602 162 +
        energyR16 12602 * radiusPolynomialRoot16 (d.w0 12602 162) (d.w1 12602 162)
          (d.w2 12602 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12602 : ℝ) ^ 16 *
        (((1876303287 / 100000000000000000000) : ℝ) + ((667476931 / 50000000000000000000)) * (126 / 100) + 2 * ((243879347 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12602) *
          (32 * (((1876303287 / 100000000000000000000) : ℝ) + (667476931 / 50000000000000000000) + (243879347 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12602

/-! A coarse bound on the actual paper statistics constant at dimension 12603. -/
namespace BstLean.Part266.Row12603
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12601 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12601 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12601 128 ≤ (12855 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12855 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12603) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12603 : ℕ))
    (by norm_num : (12603 : ℕ) ≤ 16384)
  have ht : paperTail256 12603 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12603 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12603 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12603 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12603 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12603 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12601 128 * √(2 / (12603 : ℝ)) *
      (√(12603 : ℝ) + paperT0 12603 + paperTail256 12603) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12603 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12603 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12603 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12601 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12601 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12603 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12603

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12603
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12603 (61 / 100) 162 (17 / (100 * 12603)) (26 / (10 * 12603)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12603 (61 / 100) 162 (17 / (100 * 12603)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (243818659 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (193460813 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5441880451 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12603 / 12603 * (61 / 100)) ^ 4 * inverseRadius8 (12603 - 1) /
            envelopeGap 12603 (61 / 100) 162 (17 / (100 * 12603)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12603

namespace BstLean.Part266.Row12603
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12603 162 ≤ (1167848643 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12603 162 ≤ (311691287 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (374575601 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12603 162 ≤ (468964031 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12603 162 ≤ (667317919 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12603 162 ≤ (48764259 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (243818659 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (243818659 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (193460813 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5441880451 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3672717 / 1000000000) : ℝ) ≤ √(17 / (100 * 12603) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12603) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2208251159 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3934064697 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12603) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12603) ≤ (22442491 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12603) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12603 * (162 : ℝ) ^ 2 + 26 / (10 * 12603) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12603) : ℝ)) (tA 12603 * 162 ^ 2 + 26 / (10 * 12603)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3672717 / 1000000000))) * ((243818659 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3672717 / 1000000000)) ^ 3) * ((193460813 / 125000000000000000000000))) + ((5441880451 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3672717 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12603) : ℝ)) d.D d.V d.P (√(tA 12603) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3672717 / 1000000000)) ^ 2 * (((2208251159 / 1000000000000000)) * ((3934064697 / 100000000000000000)))) + ((5441880451 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12603) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3672717 / 1000000000)) * ((243818659 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12603) : ℝ)) (tA 12603 * 162 ^ 2 + 26 / (10 * 12603)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((243818659 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3672717 / 1000000000)) ^ 2) * ((193460813 / 125000000000000000000000)) + ((5441880451 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12603) : ℝ)) (√(26 / (10 * 12603) : ℝ)) d.D d.V d.P (√(tA 12603) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3672717 / 1000000000)) * (((2208251159 / 1000000000000000)) * ((3934064697 / 100000000000000000))) + ((5441880451 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12603) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((243818659 / 50000000000000000000) : ℝ) + ((5441880451 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12603

namespace BstLean.Part266.Row12603
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12603 162 ∧
    0 ≤ (tableEnvelope C).f1 12603 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12603 162 ∧
    0 ≤ (tableEnvelope C).w1 12603 162 ∧ 0 ≤ (tableEnvelope C).w2 12603 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12603 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12603 162 ∧ 0 ≤ d.f1 12603 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12603 162 ∧ 0 ≤ d.w1 12603 162 ∧ 0 ≤ d.w2 12603 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12603 ≤ 2 * (228 / 100 : ℝ) / 12603 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12603 ≤ 2 * (370 / 100 : ℝ) / 12603 := by
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
    (completeRAData (tableEnvelope C) 12603 162).locationBound 12603 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12603 162).energyBound 12603 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12603 162) (d.f1 12603 162) d.f2 ≤
      32 * (((1167848643 / 250000000000000000) : ℝ) + (311691287 / 200000000000000000) + (374575601 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12603 162) (d.w1 12603 162)
      (d.w2 12603 162) ≤
      32 * (((468964031 / 25000000000000000000) : ℝ) + (667317919 / 50000000000000000000) + (48764259 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12603 162) (d.f1 12603 162) d.f2 ≤
      ((1167848643 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1167848643 / 250000000000000000)) * ((311691287 / 200000000000000000)) * (126 / 100) +
      2 * (((311691287 / 200000000000000000)) ^ 2 + 2 * ((1167848643 / 250000000000000000)) * ((374575601 / 1000000000000000000))) +
      6 * ((311691287 / 200000000000000000)) * ((374575601 / 1000000000000000000)) * (126 / 100) + 8 * ((374575601 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12603 162) (d.f1 12603 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12603 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12603 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12603 162) (d.f1 12603 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12603 162) (d.w1 12603 162) (d.w2 12603 162)
  have hwexpr0 : 0 ≤ d.w0 12603 162 + d.w1 12603 162 * √(π / 2) +
      2 * d.w2 12603 162 + energyR16 12603 *
      radiusPolynomialRoot16 (d.w0 12603 162) (d.w1 12603 162) (d.w2 12603 162) := by
    positivity
  constructor
  · change (12603 : ℝ) ^ 8 * (mA 12603 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12603 162) (d.f1 12603 162) d.f2 + locationR16 12603 *
        radiusPolynomialRoot16 (d.f0 12603 162) (d.f1 12603 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12603 : ℝ) ^ 8 * (mA 12603 : ℝ) ^ 8 *
        ((((1167848643 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1167848643 / 250000000000000000)) * ((311691287 / 200000000000000000)) * (126 / 100) +
          2 * (((311691287 / 200000000000000000)) ^ 2 + 2 * ((1167848643 / 250000000000000000)) * ((374575601 / 1000000000000000000))) +
          6 * ((311691287 / 200000000000000000)) * ((374575601 / 1000000000000000000)) * (126 / 100) + 8 * ((374575601 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12603) *
          (32 * (((1167848643 / 250000000000000000) : ℝ) + (311691287 / 200000000000000000) + (374575601 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12603 : ℝ) ^ 16 *
      (d.w0 12603 162 + d.w1 12603 162 * √(π / 2) + 2 * d.w2 12603 162 +
        energyR16 12603 * radiusPolynomialRoot16 (d.w0 12603 162) (d.w1 12603 162)
          (d.w2 12603 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12603 : ℝ) ^ 16 *
        (((468964031 / 25000000000000000000) : ℝ) + ((667317919 / 50000000000000000000)) * (126 / 100) + 2 * ((48764259 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12603) *
          (32 * (((468964031 / 25000000000000000000) : ℝ) + (667317919 / 50000000000000000000) + (48764259 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12603

/-! A coarse bound on the actual paper statistics constant at dimension 12604. -/
namespace BstLean.Part266.Row12604
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12602 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12602 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12602 128 ≤ (12856 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12856 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12604) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12604 : ℕ))
    (by norm_num : (12604 : ℕ) ≤ 16384)
  have ht : paperTail256 12604 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12604 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12604 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12604 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12604 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12604 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12602 128 * √(2 / (12604 : ℝ)) *
      (√(12604 : ℝ) + paperT0 12604 + paperTail256 12604) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12604 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12604 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12604 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12602 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12602 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12604 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12604

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12604
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12604 (61 / 100) 162 (17 / (100 * 12604)) (26 / (10 * 12604)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12604 (61 / 100) 162 (17 / (100 * 12604)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (243760627 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (154719537 / 100000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1087678723 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12604 / 12604 * (61 / 100)) ^ 4 * inverseRadius8 (12604 - 1) /
            envelopeGap 12604 (61 / 100) 162 (17 / (100 * 12604)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12604

namespace BstLean.Part266.Row12604
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12604 162 ≤ (4670469103 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12604 162 ≤ (1558147569 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (187250667 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12604 162 ≤ (117213117 / 6250000000000000000)
  w1 : (tableEnvelope C).w1 12604 162 ≤ (667159143 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12604 162 ≤ (487526523 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (243760627 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (243760627 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (154719537 / 100000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1087678723 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3672571 / 1000000000) : ℝ) ≤ √(17 / (100 * 12604) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12604) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2207988347 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39334404407 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12604) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12604) ≤ (3506361 / 31250000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12604) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12604 * (162 : ℝ) ^ 2 + 26 / (10 * 12604) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12604) : ℝ)) (tA 12604 * 162 ^ 2 + 26 / (10 * 12604)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3672571 / 1000000000))) * ((243760627 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3672571 / 1000000000)) ^ 3) * ((154719537 / 100000000000000000000000))) + ((1087678723 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3672571 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12604) : ℝ)) d.D d.V d.P (√(tA 12604) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3672571 / 1000000000)) ^ 2 * (((2207988347 / 1000000000000000)) * ((39334404407 / 1000000000000000000)))) + ((1087678723 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12604) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3672571 / 1000000000)) * ((243760627 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12604) : ℝ)) (tA 12604 * 162 ^ 2 + 26 / (10 * 12604)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((243760627 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3672571 / 1000000000)) ^ 2) * ((154719537 / 100000000000000000000000)) + ((1087678723 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12604) : ℝ)) (√(26 / (10 * 12604) : ℝ)) d.D d.V d.P (√(tA 12604) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3672571 / 1000000000)) * (((2207988347 / 1000000000000000)) * ((39334404407 / 1000000000000000000))) + ((1087678723 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12604) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((243760627 / 50000000000000000000) : ℝ) + ((1087678723 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12604

namespace BstLean.Part266.Row12604
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12604 162 ∧
    0 ≤ (tableEnvelope C).f1 12604 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12604 162 ∧
    0 ≤ (tableEnvelope C).w1 12604 162 ∧ 0 ≤ (tableEnvelope C).w2 12604 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12604 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12604 162 ∧ 0 ≤ d.f1 12604 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12604 162 ∧ 0 ≤ d.w1 12604 162 ∧ 0 ≤ d.w2 12604 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12604 ≤ 2 * (228 / 100 : ℝ) / 12604 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12604 ≤ 2 * (370 / 100 : ℝ) / 12604 := by
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
    (completeRAData (tableEnvelope C) 12604 162).locationBound 12604 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12604 162).energyBound 12604 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12604 162) (d.f1 12604 162) d.f2 ≤
      32 * (((4670469103 / 1000000000000000000) : ℝ) + (1558147569 / 1000000000000000000) + (187250667 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12604 162) (d.w1 12604 162)
      (d.w2 12604 162) ≤
      32 * (((117213117 / 6250000000000000000) : ℝ) + (667159143 / 50000000000000000000) + (487526523 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12604 162) (d.f1 12604 162) d.f2 ≤
      ((4670469103 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4670469103 / 1000000000000000000)) * ((1558147569 / 1000000000000000000)) * (126 / 100) +
      2 * (((1558147569 / 1000000000000000000)) ^ 2 + 2 * ((4670469103 / 1000000000000000000)) * ((187250667 / 500000000000000000))) +
      6 * ((1558147569 / 1000000000000000000)) * ((187250667 / 500000000000000000)) * (126 / 100) + 8 * ((187250667 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12604 162) (d.f1 12604 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12604 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12604 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12604 162) (d.f1 12604 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12604 162) (d.w1 12604 162) (d.w2 12604 162)
  have hwexpr0 : 0 ≤ d.w0 12604 162 + d.w1 12604 162 * √(π / 2) +
      2 * d.w2 12604 162 + energyR16 12604 *
      radiusPolynomialRoot16 (d.w0 12604 162) (d.w1 12604 162) (d.w2 12604 162) := by
    positivity
  constructor
  · change (12604 : ℝ) ^ 8 * (mA 12604 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12604 162) (d.f1 12604 162) d.f2 + locationR16 12604 *
        radiusPolynomialRoot16 (d.f0 12604 162) (d.f1 12604 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12604 : ℝ) ^ 8 * (mA 12604 : ℝ) ^ 8 *
        ((((4670469103 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4670469103 / 1000000000000000000)) * ((1558147569 / 1000000000000000000)) * (126 / 100) +
          2 * (((1558147569 / 1000000000000000000)) ^ 2 + 2 * ((4670469103 / 1000000000000000000)) * ((187250667 / 500000000000000000))) +
          6 * ((1558147569 / 1000000000000000000)) * ((187250667 / 500000000000000000)) * (126 / 100) + 8 * ((187250667 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12604) *
          (32 * (((4670469103 / 1000000000000000000) : ℝ) + (1558147569 / 1000000000000000000) + (187250667 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12604 : ℝ) ^ 16 *
      (d.w0 12604 162 + d.w1 12604 162 * √(π / 2) + 2 * d.w2 12604 162 +
        energyR16 12604 * radiusPolynomialRoot16 (d.w0 12604 162) (d.w1 12604 162)
          (d.w2 12604 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12604 : ℝ) ^ 16 *
        (((117213117 / 6250000000000000000) : ℝ) + ((667159143 / 50000000000000000000)) * (126 / 100) + 2 * ((487526523 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12604) *
          (32 * (((117213117 / 6250000000000000000) : ℝ) + (667159143 / 50000000000000000000) + (487526523 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12604

/-! A coarse bound on the actual paper statistics constant at dimension 12605. -/
namespace BstLean.Part266.Row12605
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12603 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12603 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12603 128 ≤ (12857 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12857 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12605) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12605 : ℕ))
    (by norm_num : (12605 : ℕ) ≤ 16384)
  have ht : paperTail256 12605 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12605 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12605 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12605 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12605 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12605 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12603 128 * √(2 / (12605 : ℝ)) *
      (√(12605 : ℝ) + paperT0 12605 + paperTail256 12605) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12605 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12605 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12605 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12603 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12603 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12605 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12605

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12605
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12605 (61 / 100) 162 (17 / (100 * 12605)) (26 / (10 * 12605)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12605 (61 / 100) 162 (17 / (100 * 12605)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (243702613 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (154670443 / 100000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1086981859 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12605 / 12605 * (61 / 100)) ^ 4 * inverseRadius8 (12605 - 1) /
            envelopeGap 12605 (61 / 100) 162 (17 / (100 * 12605)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12605

namespace BstLean.Part266.Row12605
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12605 162 ≤ (4669543951 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12605 162 ≤ (1557838803 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (374427089 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12605 162 ≤ (1874963773 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12605 162 ≤ (33350021 / 2500000000000000000)
  w2 : (tableEnvelope C).w2 12605 162 ≤ (487410491 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (243702613 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (243702613 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (154670443 / 100000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1086981859 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((146897 / 40000000) : ℝ) ≤ √(17 / (100 * 12605) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12605) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1103862793 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39328163319 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12605) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12605) ≤ (2243893 / 20000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12605) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12605 * (162 : ℝ) ^ 2 + 26 / (10 * 12605) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12605) : ℝ)) (tA 12605 * 162 ^ 2 + 26 / (10 * 12605)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((146897 / 40000000))) * ((243702613 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((146897 / 40000000)) ^ 3) * ((154670443 / 100000000000000000000000))) + ((1086981859 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((146897 / 40000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12605) : ℝ)) d.D d.V d.P (√(tA 12605) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((146897 / 40000000)) ^ 2 * (((1103862793 / 500000000000000)) * ((39328163319 / 1000000000000000000)))) + ((1086981859 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12605) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((146897 / 40000000)) * ((243702613 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12605) : ℝ)) (tA 12605 * 162 ^ 2 + 26 / (10 * 12605)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((243702613 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((146897 / 40000000)) ^ 2) * ((154670443 / 100000000000000000000000)) + ((1086981859 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12605) : ℝ)) (√(26 / (10 * 12605) : ℝ)) d.D d.V d.P (√(tA 12605) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((146897 / 40000000)) * (((1103862793 / 500000000000000)) * ((39328163319 / 1000000000000000000))) + ((1086981859 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12605) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((243702613 / 50000000000000000000) : ℝ) + ((1086981859 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12605

namespace BstLean.Part266.Row12605
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12605 162 ∧
    0 ≤ (tableEnvelope C).f1 12605 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12605 162 ∧
    0 ≤ (tableEnvelope C).w1 12605 162 ∧ 0 ≤ (tableEnvelope C).w2 12605 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12605 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12605 162 ∧ 0 ≤ d.f1 12605 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12605 162 ∧ 0 ≤ d.w1 12605 162 ∧ 0 ≤ d.w2 12605 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12605 ≤ 2 * (228 / 100 : ℝ) / 12605 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12605 ≤ 2 * (370 / 100 : ℝ) / 12605 := by
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
    (completeRAData (tableEnvelope C) 12605 162).locationBound 12605 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12605 162).energyBound 12605 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12605 162) (d.f1 12605 162) d.f2 ≤
      32 * (((4669543951 / 1000000000000000000) : ℝ) + (1557838803 / 1000000000000000000) + (374427089 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12605 162) (d.w1 12605 162)
      (d.w2 12605 162) ≤
      32 * (((1874963773 / 100000000000000000000) : ℝ) + (33350021 / 2500000000000000000) + (487410491 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12605 162) (d.f1 12605 162) d.f2 ≤
      ((4669543951 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4669543951 / 1000000000000000000)) * ((1557838803 / 1000000000000000000)) * (126 / 100) +
      2 * (((1557838803 / 1000000000000000000)) ^ 2 + 2 * ((4669543951 / 1000000000000000000)) * ((374427089 / 1000000000000000000))) +
      6 * ((1557838803 / 1000000000000000000)) * ((374427089 / 1000000000000000000)) * (126 / 100) + 8 * ((374427089 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12605 162) (d.f1 12605 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12605 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12605 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12605 162) (d.f1 12605 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12605 162) (d.w1 12605 162) (d.w2 12605 162)
  have hwexpr0 : 0 ≤ d.w0 12605 162 + d.w1 12605 162 * √(π / 2) +
      2 * d.w2 12605 162 + energyR16 12605 *
      radiusPolynomialRoot16 (d.w0 12605 162) (d.w1 12605 162) (d.w2 12605 162) := by
    positivity
  constructor
  · change (12605 : ℝ) ^ 8 * (mA 12605 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12605 162) (d.f1 12605 162) d.f2 + locationR16 12605 *
        radiusPolynomialRoot16 (d.f0 12605 162) (d.f1 12605 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12605 : ℝ) ^ 8 * (mA 12605 : ℝ) ^ 8 *
        ((((4669543951 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4669543951 / 1000000000000000000)) * ((1557838803 / 1000000000000000000)) * (126 / 100) +
          2 * (((1557838803 / 1000000000000000000)) ^ 2 + 2 * ((4669543951 / 1000000000000000000)) * ((374427089 / 1000000000000000000))) +
          6 * ((1557838803 / 1000000000000000000)) * ((374427089 / 1000000000000000000)) * (126 / 100) + 8 * ((374427089 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12605) *
          (32 * (((4669543951 / 1000000000000000000) : ℝ) + (1557838803 / 1000000000000000000) + (374427089 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12605 : ℝ) ^ 16 *
      (d.w0 12605 162 + d.w1 12605 162 * √(π / 2) + 2 * d.w2 12605 162 +
        energyR16 12605 * radiusPolynomialRoot16 (d.w0 12605 162) (d.w1 12605 162)
          (d.w2 12605 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12605 : ℝ) ^ 16 *
        (((1874963773 / 100000000000000000000) : ℝ) + ((33350021 / 2500000000000000000)) * (126 / 100) + 2 * ((487410491 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12605) *
          (32 * (((1874963773 / 100000000000000000000) : ℝ) + (33350021 / 2500000000000000000) + (487410491 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12605

/-! A coarse bound on the actual paper statistics constant at dimension 12606. -/
namespace BstLean.Part266.Row12606
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12604 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12604 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12604 128 ≤ (12858 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12858 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12606) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12606 : ℕ))
    (by norm_num : (12606 : ℕ) ≤ 16384)
  have ht : paperTail256 12606 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12606 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12606 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12606 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12606 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12606 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12604 128 * √(2 / (12606 : ℝ)) *
      (√(12606 : ℝ) + paperT0 12606 + paperTail256 12606) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12606 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12606 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12606 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12604 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12604 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12606 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12606

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12606
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12606 (61 / 100) 162 (17 / (100 * 12606)) (26 / (10 * 12606)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12606 (61 / 100) 162 (17 / (100 * 12606)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (121822309 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (773106843 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5431427489 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12606 / 12606 * (61 / 100)) ^ 4 * inverseRadius8 (12606 - 1) /
            envelopeGap 12606 (61 / 100) 162 (17 / (100 * 12606)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12606

namespace BstLean.Part266.Row12606
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12606 162 ≤ (2334307727 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12606 162 ≤ (1557529291 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (187176383 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12606 162 ≤ (468629269 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12606 162 ≤ (66684157 / 5000000000000000000)
  w2 : (tableEnvelope C).w2 12606 162 ≤ (243647249 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (121822309 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (121822309 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (773106843 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5431427489 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((91807 / 25000000) : ℝ) ≤ √(17 / (100 * 12606) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12606) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2207462879 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39321923733 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12606) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12606) ≤ (448743 / 4000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12606) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12606 * (162 : ℝ) ^ 2 + 26 / (10 * 12606) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12606) : ℝ)) (tA 12606 * 162 ^ 2 + 26 / (10 * 12606)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((91807 / 25000000))) * ((121822309 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((91807 / 25000000)) ^ 3) * ((773106843 / 500000000000000000000000))) + ((5431427489 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((91807 / 25000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12606) : ℝ)) d.D d.V d.P (√(tA 12606) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((91807 / 25000000)) ^ 2 * (((2207462879 / 1000000000000000)) * ((39321923733 / 1000000000000000000)))) + ((5431427489 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12606) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((91807 / 25000000)) * ((121822309 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12606) : ℝ)) (tA 12606 * 162 ^ 2 + 26 / (10 * 12606)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((121822309 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((91807 / 25000000)) ^ 2) * ((773106843 / 500000000000000000000000)) + ((5431427489 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12606) : ℝ)) (√(26 / (10 * 12606) : ℝ)) d.D d.V d.P (√(tA 12606) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((91807 / 25000000)) * (((2207462879 / 1000000000000000)) * ((39321923733 / 1000000000000000000))) + ((5431427489 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12606) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((121822309 / 25000000000000000000) : ℝ) + ((5431427489 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12606

namespace BstLean.Part266.Row12606
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12606 162 ∧
    0 ≤ (tableEnvelope C).f1 12606 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12606 162 ∧
    0 ≤ (tableEnvelope C).w1 12606 162 ∧ 0 ≤ (tableEnvelope C).w2 12606 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12606 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12606 162 ∧ 0 ≤ d.f1 12606 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12606 162 ∧ 0 ≤ d.w1 12606 162 ∧ 0 ≤ d.w2 12606 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12606 ≤ 2 * (228 / 100 : ℝ) / 12606 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12606 ≤ 2 * (370 / 100 : ℝ) / 12606 := by
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
    (completeRAData (tableEnvelope C) 12606 162).locationBound 12606 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12606 162).energyBound 12606 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12606 162) (d.f1 12606 162) d.f2 ≤
      32 * (((2334307727 / 500000000000000000) : ℝ) + (1557529291 / 1000000000000000000) + (187176383 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12606 162) (d.w1 12606 162)
      (d.w2 12606 162) ≤
      32 * (((468629269 / 25000000000000000000) : ℝ) + (66684157 / 5000000000000000000) + (243647249 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12606 162) (d.f1 12606 162) d.f2 ≤
      ((2334307727 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2334307727 / 500000000000000000)) * ((1557529291 / 1000000000000000000)) * (126 / 100) +
      2 * (((1557529291 / 1000000000000000000)) ^ 2 + 2 * ((2334307727 / 500000000000000000)) * ((187176383 / 500000000000000000))) +
      6 * ((1557529291 / 1000000000000000000)) * ((187176383 / 500000000000000000)) * (126 / 100) + 8 * ((187176383 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12606 162) (d.f1 12606 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12606 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12606 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12606 162) (d.f1 12606 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12606 162) (d.w1 12606 162) (d.w2 12606 162)
  have hwexpr0 : 0 ≤ d.w0 12606 162 + d.w1 12606 162 * √(π / 2) +
      2 * d.w2 12606 162 + energyR16 12606 *
      radiusPolynomialRoot16 (d.w0 12606 162) (d.w1 12606 162) (d.w2 12606 162) := by
    positivity
  constructor
  · change (12606 : ℝ) ^ 8 * (mA 12606 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12606 162) (d.f1 12606 162) d.f2 + locationR16 12606 *
        radiusPolynomialRoot16 (d.f0 12606 162) (d.f1 12606 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12606 : ℝ) ^ 8 * (mA 12606 : ℝ) ^ 8 *
        ((((2334307727 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2334307727 / 500000000000000000)) * ((1557529291 / 1000000000000000000)) * (126 / 100) +
          2 * (((1557529291 / 1000000000000000000)) ^ 2 + 2 * ((2334307727 / 500000000000000000)) * ((187176383 / 500000000000000000))) +
          6 * ((1557529291 / 1000000000000000000)) * ((187176383 / 500000000000000000)) * (126 / 100) + 8 * ((187176383 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12606) *
          (32 * (((2334307727 / 500000000000000000) : ℝ) + (1557529291 / 1000000000000000000) + (187176383 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12606 : ℝ) ^ 16 *
      (d.w0 12606 162 + d.w1 12606 162 * √(π / 2) + 2 * d.w2 12606 162 +
        energyR16 12606 * radiusPolynomialRoot16 (d.w0 12606 162) (d.w1 12606 162)
          (d.w2 12606 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12606 : ℝ) ^ 16 *
        (((468629269 / 25000000000000000000) : ℝ) + ((66684157 / 5000000000000000000)) * (126 / 100) + 2 * ((243647249 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12606) *
          (32 * (((468629269 / 25000000000000000000) : ℝ) + (66684157 / 5000000000000000000) + (243647249 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12606

/-! A coarse bound on the actual paper statistics constant at dimension 12607. -/
namespace BstLean.Part266.Row12607
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12605 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12605 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12605 128 ≤ (12859 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12859 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12607) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12607 : ℕ))
    (by norm_num : (12607 : ℕ) ≤ 16384)
  have ht : paperTail256 12607 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12607 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12607 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12607 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12607 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12607 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12605 128 * √(2 / (12607 : ℝ)) *
      (√(12607 : ℝ) + paperT0 12607 + paperTail256 12607) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12607 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12607 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12607 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12605 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12605 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12607 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12607

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12607
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12607 (61 / 100) 162 (17 / (100 * 12607)) (26 / (10 * 12607)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12607 (61 / 100) 162 (17 / (100 * 12607)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (243586641 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (6037981 / 3906250000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1085589639 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12607 / 12607 * (61 / 100)) ^ 4 * inverseRadius8 (12607 - 1) /
            envelopeGap 12607 (61 / 100) 162 (17 / (100 * 12607)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12607

namespace BstLean.Part266.Row12607
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12607 162 ≤ (2333845473 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12607 162 ≤ (778610363 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (187139283 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12607 162 ≤ (234258911 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 12607 162 ≤ (1333365909 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12607 162 ≤ (24358927 / 5000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (243586641 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (243586641 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (6037981 / 3906250000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1085589639 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1836067 / 500000000) : ℝ) ≤ √(17 / (100 * 12607) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12607) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2207200223 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39315685623 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12607) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12607) ≤ (28044213 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12607) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12607 * (162 : ℝ) ^ 2 + 26 / (10 * 12607) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12607) : ℝ)) (tA 12607 * 162 ^ 2 + 26 / (10 * 12607)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1836067 / 500000000))) * ((243586641 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1836067 / 500000000)) ^ 3) * ((6037981 / 3906250000000000000000))) + ((1085589639 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1836067 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12607) : ℝ)) d.D d.V d.P (√(tA 12607) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1836067 / 500000000)) ^ 2 * (((2207200223 / 1000000000000000)) * ((39315685623 / 1000000000000000000)))) + ((1085589639 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12607) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1836067 / 500000000)) * ((243586641 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12607) : ℝ)) (tA 12607 * 162 ^ 2 + 26 / (10 * 12607)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((243586641 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1836067 / 500000000)) ^ 2) * ((6037981 / 3906250000000000000000)) + ((1085589639 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12607) : ℝ)) (√(26 / (10 * 12607) : ℝ)) d.D d.V d.P (√(tA 12607) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1836067 / 500000000)) * (((2207200223 / 1000000000000000)) * ((39315685623 / 1000000000000000000))) + ((1085589639 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12607) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((243586641 / 50000000000000000000) : ℝ) + ((1085589639 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12607

namespace BstLean.Part266.Row12607
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12607 162 ∧
    0 ≤ (tableEnvelope C).f1 12607 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12607 162 ∧
    0 ≤ (tableEnvelope C).w1 12607 162 ∧ 0 ≤ (tableEnvelope C).w2 12607 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12607 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12607 162 ∧ 0 ≤ d.f1 12607 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12607 162 ∧ 0 ≤ d.w1 12607 162 ∧ 0 ≤ d.w2 12607 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12607 ≤ 2 * (228 / 100 : ℝ) / 12607 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12607 ≤ 2 * (370 / 100 : ℝ) / 12607 := by
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
    (completeRAData (tableEnvelope C) 12607 162).locationBound 12607 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12607 162).energyBound 12607 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12607 162) (d.f1 12607 162) d.f2 ≤
      32 * (((2333845473 / 500000000000000000) : ℝ) + (778610363 / 500000000000000000) + (187139283 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12607 162) (d.w1 12607 162)
      (d.w2 12607 162) ≤
      32 * (((234258911 / 12500000000000000000) : ℝ) + (1333365909 / 100000000000000000000) + (24358927 / 5000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12607 162) (d.f1 12607 162) d.f2 ≤
      ((2333845473 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2333845473 / 500000000000000000)) * ((778610363 / 500000000000000000)) * (126 / 100) +
      2 * (((778610363 / 500000000000000000)) ^ 2 + 2 * ((2333845473 / 500000000000000000)) * ((187139283 / 500000000000000000))) +
      6 * ((778610363 / 500000000000000000)) * ((187139283 / 500000000000000000)) * (126 / 100) + 8 * ((187139283 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12607 162) (d.f1 12607 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12607 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12607 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12607 162) (d.f1 12607 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12607 162) (d.w1 12607 162) (d.w2 12607 162)
  have hwexpr0 : 0 ≤ d.w0 12607 162 + d.w1 12607 162 * √(π / 2) +
      2 * d.w2 12607 162 + energyR16 12607 *
      radiusPolynomialRoot16 (d.w0 12607 162) (d.w1 12607 162) (d.w2 12607 162) := by
    positivity
  constructor
  · change (12607 : ℝ) ^ 8 * (mA 12607 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12607 162) (d.f1 12607 162) d.f2 + locationR16 12607 *
        radiusPolynomialRoot16 (d.f0 12607 162) (d.f1 12607 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12607 : ℝ) ^ 8 * (mA 12607 : ℝ) ^ 8 *
        ((((2333845473 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2333845473 / 500000000000000000)) * ((778610363 / 500000000000000000)) * (126 / 100) +
          2 * (((778610363 / 500000000000000000)) ^ 2 + 2 * ((2333845473 / 500000000000000000)) * ((187139283 / 500000000000000000))) +
          6 * ((778610363 / 500000000000000000)) * ((187139283 / 500000000000000000)) * (126 / 100) + 8 * ((187139283 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12607) *
          (32 * (((2333845473 / 500000000000000000) : ℝ) + (778610363 / 500000000000000000) + (187139283 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12607 : ℝ) ^ 16 *
      (d.w0 12607 162 + d.w1 12607 162 * √(π / 2) + 2 * d.w2 12607 162 +
        energyR16 12607 * radiusPolynomialRoot16 (d.w0 12607 162) (d.w1 12607 162)
          (d.w2 12607 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12607 : ℝ) ^ 16 *
        (((234258911 / 12500000000000000000) : ℝ) + ((1333365909 / 100000000000000000000)) * (126 / 100) + 2 * ((24358927 / 5000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12607) *
          (32 * (((234258911 / 12500000000000000000) : ℝ) + (1333365909 / 100000000000000000000) + (24358927 / 5000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12607

/-! A coarse bound on the actual paper statistics constant at dimension 12608. -/
namespace BstLean.Part266.Row12608
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12606 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12606 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12606 128 ≤ (12860 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12860 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12608) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12608 : ℕ))
    (by norm_num : (12608 : ℕ) ≤ 16384)
  have ht : paperTail256 12608 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12608 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12608 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12608 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12608 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12608 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12606 128 * √(2 / (12608 : ℝ)) *
      (√(12608 : ℝ) + paperT0 12608 + paperTail256 12608) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12608 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12608 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12608 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12606 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12606 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12608 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12608

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12608
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12608 (61 / 100) 162 (17 / (100 * 12608)) (26 / (10 * 12608)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12608 (61 / 100) 162 (17 / (100 * 12608)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (97411473 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (77261639 / 50000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5424471411 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12608 / 12608 * (61 / 100)) ^ 4 * inverseRadius8 (12608 - 1) /
            envelopeGap 12608 (61 / 100) 162 (17 / (100 * 12608)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12608

namespace BstLean.Part266.Row12608
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12608 162 ≤ (1166691689 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12608 162 ≤ (778456131 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (374204389 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12608 162 ≤ (936812827 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12608 162 ≤ (83315549 / 6250000000000000000)
  w2 : (tableEnvelope C).w2 12608 162 ≤ (24353131 / 5000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (97411473 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (97411473 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (77261639 / 50000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5424471411 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((917997 / 250000000) : ℝ) ≤ √(17 / (100 * 12608) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12608) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2206937619 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1228420281 / 31250000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12608) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12608) ≤ (56083977 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12608) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12608 * (162 : ℝ) ^ 2 + 26 / (10 * 12608) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12608) : ℝ)) (tA 12608 * 162 ^ 2 + 26 / (10 * 12608)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((917997 / 250000000))) * ((97411473 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((917997 / 250000000)) ^ 3) * ((77261639 / 50000000000000000000000))) + ((5424471411 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((917997 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12608) : ℝ)) d.D d.V d.P (√(tA 12608) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((917997 / 250000000)) ^ 2 * (((2206937619 / 1000000000000000)) * ((1228420281 / 31250000000000000)))) + ((5424471411 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12608) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((917997 / 250000000)) * ((97411473 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12608) : ℝ)) (tA 12608 * 162 ^ 2 + 26 / (10 * 12608)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((97411473 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((917997 / 250000000)) ^ 2) * ((77261639 / 50000000000000000000000)) + ((5424471411 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12608) : ℝ)) (√(26 / (10 * 12608) : ℝ)) d.D d.V d.P (√(tA 12608) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((917997 / 250000000)) * (((2206937619 / 1000000000000000)) * ((1228420281 / 31250000000000000))) + ((5424471411 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12608) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((97411473 / 20000000000000000000) : ℝ) + ((5424471411 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12608

namespace BstLean.Part266.Row12608
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12608 162 ∧
    0 ≤ (tableEnvelope C).f1 12608 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12608 162 ∧
    0 ≤ (tableEnvelope C).w1 12608 162 ∧ 0 ≤ (tableEnvelope C).w2 12608 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12608 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12608 162 ∧ 0 ≤ d.f1 12608 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12608 162 ∧ 0 ≤ d.w1 12608 162 ∧ 0 ≤ d.w2 12608 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12608 ≤ 2 * (228 / 100 : ℝ) / 12608 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12608 ≤ 2 * (370 / 100 : ℝ) / 12608 := by
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
    (completeRAData (tableEnvelope C) 12608 162).locationBound 12608 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12608 162).energyBound 12608 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12608 162) (d.f1 12608 162) d.f2 ≤
      32 * (((1166691689 / 250000000000000000) : ℝ) + (778456131 / 500000000000000000) + (374204389 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12608 162) (d.w1 12608 162)
      (d.w2 12608 162) ≤
      32 * (((936812827 / 50000000000000000000) : ℝ) + (83315549 / 6250000000000000000) + (24353131 / 5000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12608 162) (d.f1 12608 162) d.f2 ≤
      ((1166691689 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1166691689 / 250000000000000000)) * ((778456131 / 500000000000000000)) * (126 / 100) +
      2 * (((778456131 / 500000000000000000)) ^ 2 + 2 * ((1166691689 / 250000000000000000)) * ((374204389 / 1000000000000000000))) +
      6 * ((778456131 / 500000000000000000)) * ((374204389 / 1000000000000000000)) * (126 / 100) + 8 * ((374204389 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12608 162) (d.f1 12608 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12608 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12608 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12608 162) (d.f1 12608 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12608 162) (d.w1 12608 162) (d.w2 12608 162)
  have hwexpr0 : 0 ≤ d.w0 12608 162 + d.w1 12608 162 * √(π / 2) +
      2 * d.w2 12608 162 + energyR16 12608 *
      radiusPolynomialRoot16 (d.w0 12608 162) (d.w1 12608 162) (d.w2 12608 162) := by
    positivity
  constructor
  · change (12608 : ℝ) ^ 8 * (mA 12608 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12608 162) (d.f1 12608 162) d.f2 + locationR16 12608 *
        radiusPolynomialRoot16 (d.f0 12608 162) (d.f1 12608 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12608 : ℝ) ^ 8 * (mA 12608 : ℝ) ^ 8 *
        ((((1166691689 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1166691689 / 250000000000000000)) * ((778456131 / 500000000000000000)) * (126 / 100) +
          2 * (((778456131 / 500000000000000000)) ^ 2 + 2 * ((1166691689 / 250000000000000000)) * ((374204389 / 1000000000000000000))) +
          6 * ((778456131 / 500000000000000000)) * ((374204389 / 1000000000000000000)) * (126 / 100) + 8 * ((374204389 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12608) *
          (32 * (((1166691689 / 250000000000000000) : ℝ) + (778456131 / 500000000000000000) + (374204389 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12608 : ℝ) ^ 16 *
      (d.w0 12608 162 + d.w1 12608 162 * √(π / 2) + 2 * d.w2 12608 162 +
        energyR16 12608 * radiusPolynomialRoot16 (d.w0 12608 162) (d.w1 12608 162)
          (d.w2 12608 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12608 : ℝ) ^ 16 *
        (((936812827 / 50000000000000000000) : ℝ) + ((83315549 / 6250000000000000000)) * (126 / 100) + 2 * ((24353131 / 5000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12608) *
          (32 * (((936812827 / 50000000000000000000) : ℝ) + (83315549 / 6250000000000000000) + (24353131 / 5000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12608

/-! A coarse bound on the actual paper statistics constant at dimension 12609. -/
namespace BstLean.Part266.Row12609
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12607 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12607 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12607 128 ≤ (12861 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12861 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12609) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12609 : ℕ))
    (by norm_num : (12609 : ℕ) ≤ 16384)
  have ht : paperTail256 12609 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12609 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12609 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12609 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12609 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12609 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12607 128 * √(2 / (12609 : ℝ)) *
      (√(12609 : ℝ) + paperT0 12609 + paperTail256 12609) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12609 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12609 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12609 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12607 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12607 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12609 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12609

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12609
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12609 (61 / 100) 162 (17 / (100 * 12609)) (26 / (10 * 12609)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12609 (61 / 100) 162 (17 / (100 * 12609)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (97388297 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1544742619 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2710498567 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12609 / 12609 * (61 / 100)) ^ 4 * inverseRadius8 (12609 - 1) /
            envelopeGap 12609 (61 / 100) 162 (17 / (100 * 12609)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12609

namespace BstLean.Part266.Row12609
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12609 162 ≤ (4665839221 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12609 162 ≤ (31132061 / 20000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (374130133 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12609 162 ≤ (93658971 / 5000000000000000000)
  w1 : (tableEnvelope C).w1 12609 162 ≤ (333182851 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12609 162 ≤ (486946737 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (97388297 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (97388297 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1544742619 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2710498567 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3671843 / 1000000000) : ℝ) ≤ √(17 / (100 * 12609) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12609) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2206675067 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39303213851 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12609) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12609) ≤ (112159059 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12609) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12609 * (162 : ℝ) ^ 2 + 26 / (10 * 12609) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12609) : ℝ)) (tA 12609 * 162 ^ 2 + 26 / (10 * 12609)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3671843 / 1000000000))) * ((97388297 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3671843 / 1000000000)) ^ 3) * ((1544742619 / 1000000000000000000000000))) + ((2710498567 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3671843 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12609) : ℝ)) d.D d.V d.P (√(tA 12609) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3671843 / 1000000000)) ^ 2 * (((2206675067 / 1000000000000000)) * ((39303213851 / 1000000000000000000)))) + ((2710498567 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12609) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3671843 / 1000000000)) * ((97388297 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12609) : ℝ)) (tA 12609 * 162 ^ 2 + 26 / (10 * 12609)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((97388297 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3671843 / 1000000000)) ^ 2) * ((1544742619 / 1000000000000000000000000)) + ((2710498567 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12609) : ℝ)) (√(26 / (10 * 12609) : ℝ)) d.D d.V d.P (√(tA 12609) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3671843 / 1000000000)) * (((2206675067 / 1000000000000000)) * ((39303213851 / 1000000000000000000))) + ((2710498567 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12609) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((97388297 / 20000000000000000000) : ℝ) + ((2710498567 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12609

namespace BstLean.Part266.Row12609
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12609 162 ∧
    0 ≤ (tableEnvelope C).f1 12609 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12609 162 ∧
    0 ≤ (tableEnvelope C).w1 12609 162 ∧ 0 ≤ (tableEnvelope C).w2 12609 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12609 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12609 162 ∧ 0 ≤ d.f1 12609 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12609 162 ∧ 0 ≤ d.w1 12609 162 ∧ 0 ≤ d.w2 12609 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12609 ≤ 2 * (228 / 100 : ℝ) / 12609 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12609 ≤ 2 * (370 / 100 : ℝ) / 12609 := by
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
    (completeRAData (tableEnvelope C) 12609 162).locationBound 12609 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12609 162).energyBound 12609 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12609 162) (d.f1 12609 162) d.f2 ≤
      32 * (((4665839221 / 1000000000000000000) : ℝ) + (31132061 / 20000000000000000) + (374130133 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12609 162) (d.w1 12609 162)
      (d.w2 12609 162) ≤
      32 * (((93658971 / 5000000000000000000) : ℝ) + (333182851 / 25000000000000000000) + (486946737 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12609 162) (d.f1 12609 162) d.f2 ≤
      ((4665839221 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4665839221 / 1000000000000000000)) * ((31132061 / 20000000000000000)) * (126 / 100) +
      2 * (((31132061 / 20000000000000000)) ^ 2 + 2 * ((4665839221 / 1000000000000000000)) * ((374130133 / 1000000000000000000))) +
      6 * ((31132061 / 20000000000000000)) * ((374130133 / 1000000000000000000)) * (126 / 100) + 8 * ((374130133 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12609 162) (d.f1 12609 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12609 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12609 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12609 162) (d.f1 12609 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12609 162) (d.w1 12609 162) (d.w2 12609 162)
  have hwexpr0 : 0 ≤ d.w0 12609 162 + d.w1 12609 162 * √(π / 2) +
      2 * d.w2 12609 162 + energyR16 12609 *
      radiusPolynomialRoot16 (d.w0 12609 162) (d.w1 12609 162) (d.w2 12609 162) := by
    positivity
  constructor
  · change (12609 : ℝ) ^ 8 * (mA 12609 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12609 162) (d.f1 12609 162) d.f2 + locationR16 12609 *
        radiusPolynomialRoot16 (d.f0 12609 162) (d.f1 12609 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12609 : ℝ) ^ 8 * (mA 12609 : ℝ) ^ 8 *
        ((((4665839221 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4665839221 / 1000000000000000000)) * ((31132061 / 20000000000000000)) * (126 / 100) +
          2 * (((31132061 / 20000000000000000)) ^ 2 + 2 * ((4665839221 / 1000000000000000000)) * ((374130133 / 1000000000000000000))) +
          6 * ((31132061 / 20000000000000000)) * ((374130133 / 1000000000000000000)) * (126 / 100) + 8 * ((374130133 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12609) *
          (32 * (((4665839221 / 1000000000000000000) : ℝ) + (31132061 / 20000000000000000) + (374130133 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12609 : ℝ) ^ 16 *
      (d.w0 12609 162 + d.w1 12609 162 * √(π / 2) + 2 * d.w2 12609 162 +
        energyR16 12609 * radiusPolynomialRoot16 (d.w0 12609 162) (d.w1 12609 162)
          (d.w2 12609 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12609 : ℝ) ^ 16 *
        (((93658971 / 5000000000000000000) : ℝ) + ((333182851 / 25000000000000000000)) * (126 / 100) + 2 * ((486946737 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12609) *
          (32 * (((93658971 / 5000000000000000000) : ℝ) + (333182851 / 25000000000000000000) + (486946737 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12609

/-! A coarse bound on the actual paper statistics constant at dimension 12610. -/
namespace BstLean.Part266.Row12610
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12608 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12608 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12608 128 ≤ (12862 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12862 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12610) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12610 : ℕ))
    (by norm_num : (12610 : ℕ) ≤ 16384)
  have ht : paperTail256 12610 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12610 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12610 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12610 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12610 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12610 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12608 128 * √(2 / (12610 : ℝ)) *
      (√(12610 : ℝ) + paperT0 12610 + paperTail256 12610) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12610 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12610 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12610 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12608 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12608 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12610 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12610

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12610
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12610 (61 / 100) 162 (17 / (100 * 12610)) (26 / (10 * 12610)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12610 (61 / 100) 162 (17 / (100 * 12610)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (243412821 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (386063163 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5417525363 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12610 / 12610 * (61 / 100)) ^ 4 * inverseRadius8 (12610 - 1) /
            envelopeGap 12610 (61 / 100) 162 (17 / (100 * 12610)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12610

namespace BstLean.Part266.Row12610
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12610 162 ≤ (583114459 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12610 162 ≤ (1556294787 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (374056001 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12610 162 ≤ (374546819 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12610 162 ≤ (1332414493 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12610 162 ≤ (48683089 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (243412821 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (243412821 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (386063163 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5417525363 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3671697 / 1000000000) : ℝ) ≤ √(17 / (100 * 12610) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12610) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (275801571 / 125000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3929698019 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12610) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12610) ≤ (28037541 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12610) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12610 * (162 : ℝ) ^ 2 + 26 / (10 * 12610) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12610) : ℝ)) (tA 12610 * 162 ^ 2 + 26 / (10 * 12610)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3671697 / 1000000000))) * ((243412821 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3671697 / 1000000000)) ^ 3) * ((386063163 / 250000000000000000000000))) + ((5417525363 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3671697 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12610) : ℝ)) d.D d.V d.P (√(tA 12610) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3671697 / 1000000000)) ^ 2 * (((275801571 / 125000000000000)) * ((3929698019 / 100000000000000000)))) + ((5417525363 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12610) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3671697 / 1000000000)) * ((243412821 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12610) : ℝ)) (tA 12610 * 162 ^ 2 + 26 / (10 * 12610)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((243412821 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3671697 / 1000000000)) ^ 2) * ((386063163 / 250000000000000000000000)) + ((5417525363 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12610) : ℝ)) (√(26 / (10 * 12610) : ℝ)) d.D d.V d.P (√(tA 12610) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3671697 / 1000000000)) * (((275801571 / 125000000000000)) * ((3929698019 / 100000000000000000))) + ((5417525363 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12610) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((243412821 / 50000000000000000000) : ℝ) + ((5417525363 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12610

namespace BstLean.Part266.Row12610
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12610 162 ∧
    0 ≤ (tableEnvelope C).f1 12610 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12610 162 ∧
    0 ≤ (tableEnvelope C).w1 12610 162 ∧ 0 ≤ (tableEnvelope C).w2 12610 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12610 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12610 162 ∧ 0 ≤ d.f1 12610 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12610 162 ∧ 0 ≤ d.w1 12610 162 ∧ 0 ≤ d.w2 12610 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12610 ≤ 2 * (228 / 100 : ℝ) / 12610 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12610 ≤ 2 * (370 / 100 : ℝ) / 12610 := by
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
    (completeRAData (tableEnvelope C) 12610 162).locationBound 12610 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12610 162).energyBound 12610 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12610 162) (d.f1 12610 162) d.f2 ≤
      32 * (((583114459 / 125000000000000000) : ℝ) + (1556294787 / 1000000000000000000) + (374056001 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12610 162) (d.w1 12610 162)
      (d.w2 12610 162) ≤
      32 * (((374546819 / 20000000000000000000) : ℝ) + (1332414493 / 100000000000000000000) + (48683089 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12610 162) (d.f1 12610 162) d.f2 ≤
      ((583114459 / 125000000000000000) : ℝ) ^ 2 + 2 * ((583114459 / 125000000000000000)) * ((1556294787 / 1000000000000000000)) * (126 / 100) +
      2 * (((1556294787 / 1000000000000000000)) ^ 2 + 2 * ((583114459 / 125000000000000000)) * ((374056001 / 1000000000000000000))) +
      6 * ((1556294787 / 1000000000000000000)) * ((374056001 / 1000000000000000000)) * (126 / 100) + 8 * ((374056001 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12610 162) (d.f1 12610 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12610 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12610 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12610 162) (d.f1 12610 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12610 162) (d.w1 12610 162) (d.w2 12610 162)
  have hwexpr0 : 0 ≤ d.w0 12610 162 + d.w1 12610 162 * √(π / 2) +
      2 * d.w2 12610 162 + energyR16 12610 *
      radiusPolynomialRoot16 (d.w0 12610 162) (d.w1 12610 162) (d.w2 12610 162) := by
    positivity
  constructor
  · change (12610 : ℝ) ^ 8 * (mA 12610 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12610 162) (d.f1 12610 162) d.f2 + locationR16 12610 *
        radiusPolynomialRoot16 (d.f0 12610 162) (d.f1 12610 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12610 : ℝ) ^ 8 * (mA 12610 : ℝ) ^ 8 *
        ((((583114459 / 125000000000000000) : ℝ) ^ 2 + 2 * ((583114459 / 125000000000000000)) * ((1556294787 / 1000000000000000000)) * (126 / 100) +
          2 * (((1556294787 / 1000000000000000000)) ^ 2 + 2 * ((583114459 / 125000000000000000)) * ((374056001 / 1000000000000000000))) +
          6 * ((1556294787 / 1000000000000000000)) * ((374056001 / 1000000000000000000)) * (126 / 100) + 8 * ((374056001 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12610) *
          (32 * (((583114459 / 125000000000000000) : ℝ) + (1556294787 / 1000000000000000000) + (374056001 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12610 : ℝ) ^ 16 *
      (d.w0 12610 162 + d.w1 12610 162 * √(π / 2) + 2 * d.w2 12610 162 +
        energyR16 12610 * radiusPolynomialRoot16 (d.w0 12610 162) (d.w1 12610 162)
          (d.w2 12610 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12610 : ℝ) ^ 16 *
        (((374546819 / 20000000000000000000) : ℝ) + ((1332414493 / 100000000000000000000)) * (126 / 100) + 2 * ((48683089 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12610) *
          (32 * (((374546819 / 20000000000000000000) : ℝ) + (1332414493 / 100000000000000000000) + (48683089 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12610

/-! A coarse bound on the actual paper statistics constant at dimension 12611. -/
namespace BstLean.Part266.Row12611
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12609 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12609 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12609 128 ≤ (12863 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12863 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12611) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12611 : ℕ))
    (by norm_num : (12611 : ℕ) ≤ 16384)
  have ht : paperTail256 12611 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12611 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12611 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12611 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12611 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12611 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12609 128 * √(2 / (12611 : ℝ)) *
      (√(12611 : ℝ) + paperT0 12611 + paperTail256 12611) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12611 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12611 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12611 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12609 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12609 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12611 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12611

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12611
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12611 (61 / 100) 162 (17 / (100 * 12611)) (26 / (10 * 12611)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12611 (61 / 100) 162 (17 / (100 * 12611)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (97341967 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (4824259 / 3125000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (169189253 / 31250000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12611 / 12611 * (61 / 100)) ^ 4 * inverseRadius8 (12611 - 1) /
            envelopeGap 12611 (61 / 100) 162 (17 / (100 * 12611)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12611

namespace BstLean.Part266.Row12611
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12611 162 ≤ (4663988779 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12611 162 ≤ (1555985777 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (373981789 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12611 162 ≤ (187228817 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 12611 162 ≤ (1332097327 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12611 162 ≤ (12167877 / 2500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (97341967 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (97341967 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (4824259 / 3125000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (169189253 / 31250000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((7171 / 1953125) : ℝ) ≤ √(17 / (100 * 12611) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12611) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (55153753 / 25000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39290748021 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12611) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12611) ≤ (112141271 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12611) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12611 * (162 : ℝ) ^ 2 + 26 / (10 * 12611) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12611) : ℝ)) (tA 12611 * 162 ^ 2 + 26 / (10 * 12611)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((7171 / 1953125))) * ((97341967 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((7171 / 1953125)) ^ 3) * ((4824259 / 3125000000000000000000))) + ((169189253 / 31250000000000000000000)) * (3 / 2 * (39895 / 100000) / ((7171 / 1953125)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12611) : ℝ)) d.D d.V d.P (√(tA 12611) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((7171 / 1953125)) ^ 2 * (((55153753 / 25000000000000)) * ((39290748021 / 1000000000000000000)))) + ((169189253 / 31250000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12611) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((7171 / 1953125)) * ((97341967 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12611) : ℝ)) (tA 12611 * 162 ^ 2 + 26 / (10 * 12611)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((97341967 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((7171 / 1953125)) ^ 2) * ((4824259 / 3125000000000000000000)) + ((169189253 / 31250000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12611) : ℝ)) (√(26 / (10 * 12611) : ℝ)) d.D d.V d.P (√(tA 12611) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((7171 / 1953125)) * (((55153753 / 25000000000000)) * ((39290748021 / 1000000000000000000))) + ((169189253 / 31250000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12611) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((97341967 / 20000000000000000000) : ℝ) + ((169189253 / 31250000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12611

namespace BstLean.Part266.Row12611
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12611 162 ∧
    0 ≤ (tableEnvelope C).f1 12611 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12611 162 ∧
    0 ≤ (tableEnvelope C).w1 12611 162 ∧ 0 ≤ (tableEnvelope C).w2 12611 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12611 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12611 162 ∧ 0 ≤ d.f1 12611 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12611 162 ∧ 0 ≤ d.w1 12611 162 ∧ 0 ≤ d.w2 12611 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12611 ≤ 2 * (228 / 100 : ℝ) / 12611 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12611 ≤ 2 * (370 / 100 : ℝ) / 12611 := by
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
    (completeRAData (tableEnvelope C) 12611 162).locationBound 12611 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12611 162).energyBound 12611 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12611 162) (d.f1 12611 162) d.f2 ≤
      32 * (((4663988779 / 1000000000000000000) : ℝ) + (1555985777 / 1000000000000000000) + (373981789 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12611 162) (d.w1 12611 162)
      (d.w2 12611 162) ≤
      32 * (((187228817 / 10000000000000000000) : ℝ) + (1332097327 / 100000000000000000000) + (12167877 / 2500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12611 162) (d.f1 12611 162) d.f2 ≤
      ((4663988779 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4663988779 / 1000000000000000000)) * ((1555985777 / 1000000000000000000)) * (126 / 100) +
      2 * (((1555985777 / 1000000000000000000)) ^ 2 + 2 * ((4663988779 / 1000000000000000000)) * ((373981789 / 1000000000000000000))) +
      6 * ((1555985777 / 1000000000000000000)) * ((373981789 / 1000000000000000000)) * (126 / 100) + 8 * ((373981789 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12611 162) (d.f1 12611 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12611 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12611 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12611 162) (d.f1 12611 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12611 162) (d.w1 12611 162) (d.w2 12611 162)
  have hwexpr0 : 0 ≤ d.w0 12611 162 + d.w1 12611 162 * √(π / 2) +
      2 * d.w2 12611 162 + energyR16 12611 *
      radiusPolynomialRoot16 (d.w0 12611 162) (d.w1 12611 162) (d.w2 12611 162) := by
    positivity
  constructor
  · change (12611 : ℝ) ^ 8 * (mA 12611 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12611 162) (d.f1 12611 162) d.f2 + locationR16 12611 *
        radiusPolynomialRoot16 (d.f0 12611 162) (d.f1 12611 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12611 : ℝ) ^ 8 * (mA 12611 : ℝ) ^ 8 *
        ((((4663988779 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4663988779 / 1000000000000000000)) * ((1555985777 / 1000000000000000000)) * (126 / 100) +
          2 * (((1555985777 / 1000000000000000000)) ^ 2 + 2 * ((4663988779 / 1000000000000000000)) * ((373981789 / 1000000000000000000))) +
          6 * ((1555985777 / 1000000000000000000)) * ((373981789 / 1000000000000000000)) * (126 / 100) + 8 * ((373981789 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12611) *
          (32 * (((4663988779 / 1000000000000000000) : ℝ) + (1555985777 / 1000000000000000000) + (373981789 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12611 : ℝ) ^ 16 *
      (d.w0 12611 162 + d.w1 12611 162 * √(π / 2) + 2 * d.w2 12611 162 +
        energyR16 12611 * radiusPolynomialRoot16 (d.w0 12611 162) (d.w1 12611 162)
          (d.w2 12611 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12611 : ℝ) ^ 16 *
        (((187228817 / 10000000000000000000) : ℝ) + ((1332097327 / 100000000000000000000)) * (126 / 100) + 2 * ((12167877 / 2500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12611) *
          (32 * (((187228817 / 10000000000000000000) : ℝ) + (1332097327 / 100000000000000000000) + (12167877 / 2500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12611

/-! A coarse bound on the actual paper statistics constant at dimension 12612. -/
namespace BstLean.Part266.Row12612
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12610 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12610 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12610 128 ≤ (12864 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12864 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12612) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12612 : ℕ))
    (by norm_num : (12612 : ℕ) ≤ 16384)
  have ht : paperTail256 12612 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12612 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12612 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12612 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12612 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12612 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12610 128 * √(2 / (12612 : ℝ)) *
      (√(12612 : ℝ) + paperT0 12612 + paperTail256 12612) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12612 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12612 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12612 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12610 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12610 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12612 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12612

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12612
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12612 (61 / 100) 162 (17 / (100 * 12612)) (26 / (10 * 12612)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12612 (61 / 100) 162 (17 / (100 * 12612)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (97318813 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (771636651 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (541058933 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12612 / 12612 * (61 / 100)) ^ 4 * inverseRadius8 (12612 - 1) /
            envelopeGap 12612 (61 / 100) 162 (17 / (100 * 12612)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12612

namespace BstLean.Part266.Row12612
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12612 162 ≤ (291441617 / 62500000000000000)
  f1 : (tableEnvelope C).f1 12612 162 ≤ (777838857 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (373907701 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12612 162 ≤ (935921577 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12612 162 ≤ (133178063 / 10000000000000000000)
  w2 : (tableEnvelope C).w2 12612 162 ≤ (486599307 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (97318813 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (97318813 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (771636651 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (541058933 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1835703 / 500000000) : ℝ) ≤ √(17 / (100 * 12612) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12612) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (551471931 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9821129333 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12612) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12612) ≤ (112132379 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12612) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12612 * (162 : ℝ) ^ 2 + 26 / (10 * 12612) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12612) : ℝ)) (tA 12612 * 162 ^ 2 + 26 / (10 * 12612)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1835703 / 500000000))) * ((97318813 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1835703 / 500000000)) ^ 3) * ((771636651 / 500000000000000000000000))) + ((541058933 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1835703 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12612) : ℝ)) d.D d.V d.P (√(tA 12612) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1835703 / 500000000)) ^ 2 * (((551471931 / 250000000000000)) * ((9821129333 / 250000000000000000)))) + ((541058933 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12612) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1835703 / 500000000)) * ((97318813 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12612) : ℝ)) (tA 12612 * 162 ^ 2 + 26 / (10 * 12612)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((97318813 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1835703 / 500000000)) ^ 2) * ((771636651 / 500000000000000000000000)) + ((541058933 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12612) : ℝ)) (√(26 / (10 * 12612) : ℝ)) d.D d.V d.P (√(tA 12612) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1835703 / 500000000)) * (((551471931 / 250000000000000)) * ((9821129333 / 250000000000000000))) + ((541058933 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12612) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((97318813 / 20000000000000000000) : ℝ) + ((541058933 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12612

namespace BstLean.Part266.Row12612
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12612 162 ∧
    0 ≤ (tableEnvelope C).f1 12612 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12612 162 ∧
    0 ≤ (tableEnvelope C).w1 12612 162 ∧ 0 ≤ (tableEnvelope C).w2 12612 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12612 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12612 162 ∧ 0 ≤ d.f1 12612 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12612 162 ∧ 0 ≤ d.w1 12612 162 ∧ 0 ≤ d.w2 12612 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12612 ≤ 2 * (228 / 100 : ℝ) / 12612 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12612 ≤ 2 * (370 / 100 : ℝ) / 12612 := by
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
    (completeRAData (tableEnvelope C) 12612 162).locationBound 12612 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12612 162).energyBound 12612 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12612 162) (d.f1 12612 162) d.f2 ≤
      32 * (((291441617 / 62500000000000000) : ℝ) + (777838857 / 500000000000000000) + (373907701 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12612 162) (d.w1 12612 162)
      (d.w2 12612 162) ≤
      32 * (((935921577 / 50000000000000000000) : ℝ) + (133178063 / 10000000000000000000) + (486599307 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12612 162) (d.f1 12612 162) d.f2 ≤
      ((291441617 / 62500000000000000) : ℝ) ^ 2 + 2 * ((291441617 / 62500000000000000)) * ((777838857 / 500000000000000000)) * (126 / 100) +
      2 * (((777838857 / 500000000000000000)) ^ 2 + 2 * ((291441617 / 62500000000000000)) * ((373907701 / 1000000000000000000))) +
      6 * ((777838857 / 500000000000000000)) * ((373907701 / 1000000000000000000)) * (126 / 100) + 8 * ((373907701 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12612 162) (d.f1 12612 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12612 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12612 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12612 162) (d.f1 12612 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12612 162) (d.w1 12612 162) (d.w2 12612 162)
  have hwexpr0 : 0 ≤ d.w0 12612 162 + d.w1 12612 162 * √(π / 2) +
      2 * d.w2 12612 162 + energyR16 12612 *
      radiusPolynomialRoot16 (d.w0 12612 162) (d.w1 12612 162) (d.w2 12612 162) := by
    positivity
  constructor
  · change (12612 : ℝ) ^ 8 * (mA 12612 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12612 162) (d.f1 12612 162) d.f2 + locationR16 12612 *
        radiusPolynomialRoot16 (d.f0 12612 162) (d.f1 12612 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12612 : ℝ) ^ 8 * (mA 12612 : ℝ) ^ 8 *
        ((((291441617 / 62500000000000000) : ℝ) ^ 2 + 2 * ((291441617 / 62500000000000000)) * ((777838857 / 500000000000000000)) * (126 / 100) +
          2 * (((777838857 / 500000000000000000)) ^ 2 + 2 * ((291441617 / 62500000000000000)) * ((373907701 / 1000000000000000000))) +
          6 * ((777838857 / 500000000000000000)) * ((373907701 / 1000000000000000000)) * (126 / 100) + 8 * ((373907701 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12612) *
          (32 * (((291441617 / 62500000000000000) : ℝ) + (777838857 / 500000000000000000) + (373907701 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12612 : ℝ) ^ 16 *
      (d.w0 12612 162 + d.w1 12612 162 * √(π / 2) + 2 * d.w2 12612 162 +
        energyR16 12612 * radiusPolynomialRoot16 (d.w0 12612 162) (d.w1 12612 162)
          (d.w2 12612 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12612 : ℝ) ^ 16 *
        (((935921577 / 50000000000000000000) : ℝ) + ((133178063 / 10000000000000000000)) * (126 / 100) + 2 * ((486599307 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12612) *
          (32 * (((935921577 / 50000000000000000000) : ℝ) + (133178063 / 10000000000000000000) + (486599307 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12612

/-! A coarse bound on the actual paper statistics constant at dimension 12613. -/
namespace BstLean.Part266.Row12613
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12611 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12611 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12611 128 ≤ (12865 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12865 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12613) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12613 : ℕ))
    (by norm_num : (12613 : ℕ) ≤ 16384)
  have ht : paperTail256 12613 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12613 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12613 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12613 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12613 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12613 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12611 128 * √(2 / (12613 : ℝ)) *
      (√(12613 : ℝ) + paperT0 12613 + paperTail256 12613) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12613 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12613 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12613 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12611 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12611 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12613 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12613

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12613
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12613 (61 / 100) 162 (17 / (100 * 12613)) (26 / (10 * 12613)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12613 (61 / 100) 162 (17 / (100 * 12613)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (121619583 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1542783917 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (675890633 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12613 / 12613 * (61 / 100)) ^ 4 * inverseRadius8 (12613 - 1) /
            envelopeGap 12613 (61 / 100) 162 (17 / (100 * 12613)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12613

namespace BstLean.Part266.Row12613
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12613 162 ≤ (4662139617 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12613 162 ≤ (194421113 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (186916767 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12613 162 ≤ (935698769 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12613 162 ≤ (1331463677 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12613 162 ≤ (48648357 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (121619583 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (121619583 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1542783917 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (675890633 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3671261 / 1000000000) : ℝ) ≤ √(17 / (100 * 12613) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12613) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2205625381 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (2454893007 / 62500000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12613) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12613) ≤ (112123489 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12613) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12613 * (162 : ℝ) ^ 2 + 26 / (10 * 12613) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12613) : ℝ)) (tA 12613 * 162 ^ 2 + 26 / (10 * 12613)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3671261 / 1000000000))) * ((121619583 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3671261 / 1000000000)) ^ 3) * ((1542783917 / 1000000000000000000000000))) + ((675890633 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3671261 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12613) : ℝ)) d.D d.V d.P (√(tA 12613) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3671261 / 1000000000)) ^ 2 * (((2205625381 / 1000000000000000)) * ((2454893007 / 62500000000000000)))) + ((675890633 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12613) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3671261 / 1000000000)) * ((121619583 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12613) : ℝ)) (tA 12613 * 162 ^ 2 + 26 / (10 * 12613)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((121619583 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3671261 / 1000000000)) ^ 2) * ((1542783917 / 1000000000000000000000000)) + ((675890633 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12613) : ℝ)) (√(26 / (10 * 12613) : ℝ)) d.D d.V d.P (√(tA 12613) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3671261 / 1000000000)) * (((2205625381 / 1000000000000000)) * ((2454893007 / 62500000000000000))) + ((675890633 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12613) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((121619583 / 25000000000000000000) : ℝ) + ((675890633 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12613

namespace BstLean.Part266.Row12613
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12613 162 ∧
    0 ≤ (tableEnvelope C).f1 12613 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12613 162 ∧
    0 ≤ (tableEnvelope C).w1 12613 162 ∧ 0 ≤ (tableEnvelope C).w2 12613 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12613 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12613 162 ∧ 0 ≤ d.f1 12613 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12613 162 ∧ 0 ≤ d.w1 12613 162 ∧ 0 ≤ d.w2 12613 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12613 ≤ 2 * (228 / 100 : ℝ) / 12613 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12613 ≤ 2 * (370 / 100 : ℝ) / 12613 := by
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
    (completeRAData (tableEnvelope C) 12613 162).locationBound 12613 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12613 162).energyBound 12613 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12613 162) (d.f1 12613 162) d.f2 ≤
      32 * (((4662139617 / 1000000000000000000) : ℝ) + (194421113 / 125000000000000000) + (186916767 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12613 162) (d.w1 12613 162)
      (d.w2 12613 162) ≤
      32 * (((935698769 / 50000000000000000000) : ℝ) + (1331463677 / 100000000000000000000) + (48648357 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12613 162) (d.f1 12613 162) d.f2 ≤
      ((4662139617 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4662139617 / 1000000000000000000)) * ((194421113 / 125000000000000000)) * (126 / 100) +
      2 * (((194421113 / 125000000000000000)) ^ 2 + 2 * ((4662139617 / 1000000000000000000)) * ((186916767 / 500000000000000000))) +
      6 * ((194421113 / 125000000000000000)) * ((186916767 / 500000000000000000)) * (126 / 100) + 8 * ((186916767 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12613 162) (d.f1 12613 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12613 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12613 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12613 162) (d.f1 12613 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12613 162) (d.w1 12613 162) (d.w2 12613 162)
  have hwexpr0 : 0 ≤ d.w0 12613 162 + d.w1 12613 162 * √(π / 2) +
      2 * d.w2 12613 162 + energyR16 12613 *
      radiusPolynomialRoot16 (d.w0 12613 162) (d.w1 12613 162) (d.w2 12613 162) := by
    positivity
  constructor
  · change (12613 : ℝ) ^ 8 * (mA 12613 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12613 162) (d.f1 12613 162) d.f2 + locationR16 12613 *
        radiusPolynomialRoot16 (d.f0 12613 162) (d.f1 12613 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12613 : ℝ) ^ 8 * (mA 12613 : ℝ) ^ 8 *
        ((((4662139617 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4662139617 / 1000000000000000000)) * ((194421113 / 125000000000000000)) * (126 / 100) +
          2 * (((194421113 / 125000000000000000)) ^ 2 + 2 * ((4662139617 / 1000000000000000000)) * ((186916767 / 500000000000000000))) +
          6 * ((194421113 / 125000000000000000)) * ((186916767 / 500000000000000000)) * (126 / 100) + 8 * ((186916767 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12613) *
          (32 * (((4662139617 / 1000000000000000000) : ℝ) + (194421113 / 125000000000000000) + (186916767 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12613 : ℝ) ^ 16 *
      (d.w0 12613 162 + d.w1 12613 162 * √(π / 2) + 2 * d.w2 12613 162 +
        energyR16 12613 * radiusPolynomialRoot16 (d.w0 12613 162) (d.w1 12613 162)
          (d.w2 12613 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12613 : ℝ) ^ 16 *
        (((935698769 / 50000000000000000000) : ℝ) + ((1331463677 / 100000000000000000000)) * (126 / 100) + 2 * ((48648357 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12613) *
          (32 * (((935698769 / 50000000000000000000) : ℝ) + (1331463677 / 100000000000000000000) + (48648357 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12613

/-! A coarse bound on the actual paper statistics constant at dimension 12614. -/
namespace BstLean.Part266.Row12614
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12612 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12612 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12612 128 ≤ (12866 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12866 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12614) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12614 : ℕ))
    (by norm_num : (12614 : ℕ) ≤ 16384)
  have ht : paperTail256 12614 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12614 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12614 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12614 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12614 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12614 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12612 128 * √(2 / (12614 : ℝ)) *
      (√(12614 : ℝ) + paperT0 12614 + paperTail256 12614) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12614 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12614 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12614 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12612 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12612 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12614 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12614

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12614
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12614 (61 / 100) 162 (17 / (100 * 12614)) (26 / (10 * 12614)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12614 (61 / 100) 162 (17 / (100 * 12614)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (97272527 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1542294727 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (84432239 / 15625000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12614 / 12614 * (61 / 100)) ^ 4 * inverseRadius8 (12614 - 1) /
            envelopeGap 12614 (61 / 100) 162 (17 / (100 * 12614)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12614

namespace BstLean.Part266.Row12614
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12614 162 ≤ (4661217349 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12614 162 ≤ (1555061041 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (373759491 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12614 162 ≤ (187095283 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 12614 162 ≤ (665573597 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12614 162 ≤ (48636787 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (97272527 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (97272527 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1542294727 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (84432239 / 15625000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((734223 / 200000000) : ℝ) ≤ √(17 / (100 * 12614) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12614) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2205363089 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39272060387 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12614) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12614) ≤ (560573 / 5000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12614) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12614 * (162 : ℝ) ^ 2 + 26 / (10 * 12614) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12614) : ℝ)) (tA 12614 * 162 ^ 2 + 26 / (10 * 12614)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((734223 / 200000000))) * ((97272527 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((734223 / 200000000)) ^ 3) * ((1542294727 / 1000000000000000000000000))) + ((84432239 / 15625000000000000000000)) * (3 / 2 * (39895 / 100000) / ((734223 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12614) : ℝ)) d.D d.V d.P (√(tA 12614) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((734223 / 200000000)) ^ 2 * (((2205363089 / 1000000000000000)) * ((39272060387 / 1000000000000000000)))) + ((84432239 / 15625000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12614) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((734223 / 200000000)) * ((97272527 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12614) : ℝ)) (tA 12614 * 162 ^ 2 + 26 / (10 * 12614)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((97272527 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((734223 / 200000000)) ^ 2) * ((1542294727 / 1000000000000000000000000)) + ((84432239 / 15625000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12614) : ℝ)) (√(26 / (10 * 12614) : ℝ)) d.D d.V d.P (√(tA 12614) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((734223 / 200000000)) * (((2205363089 / 1000000000000000)) * ((39272060387 / 1000000000000000000))) + ((84432239 / 15625000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12614) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((97272527 / 20000000000000000000) : ℝ) + ((84432239 / 15625000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12614

namespace BstLean.Part266.Row12614
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12614 162 ∧
    0 ≤ (tableEnvelope C).f1 12614 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12614 162 ∧
    0 ≤ (tableEnvelope C).w1 12614 162 ∧ 0 ≤ (tableEnvelope C).w2 12614 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12614 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12614 162 ∧ 0 ≤ d.f1 12614 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12614 162 ∧ 0 ≤ d.w1 12614 162 ∧ 0 ≤ d.w2 12614 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12614 ≤ 2 * (228 / 100 : ℝ) / 12614 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12614 ≤ 2 * (370 / 100 : ℝ) / 12614 := by
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
    (completeRAData (tableEnvelope C) 12614 162).locationBound 12614 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12614 162).energyBound 12614 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12614 162) (d.f1 12614 162) d.f2 ≤
      32 * (((4661217349 / 1000000000000000000) : ℝ) + (1555061041 / 1000000000000000000) + (373759491 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12614 162) (d.w1 12614 162)
      (d.w2 12614 162) ≤
      32 * (((187095283 / 10000000000000000000) : ℝ) + (665573597 / 50000000000000000000) + (48636787 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12614 162) (d.f1 12614 162) d.f2 ≤
      ((4661217349 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4661217349 / 1000000000000000000)) * ((1555061041 / 1000000000000000000)) * (126 / 100) +
      2 * (((1555061041 / 1000000000000000000)) ^ 2 + 2 * ((4661217349 / 1000000000000000000)) * ((373759491 / 1000000000000000000))) +
      6 * ((1555061041 / 1000000000000000000)) * ((373759491 / 1000000000000000000)) * (126 / 100) + 8 * ((373759491 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12614 162) (d.f1 12614 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12614 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12614 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12614 162) (d.f1 12614 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12614 162) (d.w1 12614 162) (d.w2 12614 162)
  have hwexpr0 : 0 ≤ d.w0 12614 162 + d.w1 12614 162 * √(π / 2) +
      2 * d.w2 12614 162 + energyR16 12614 *
      radiusPolynomialRoot16 (d.w0 12614 162) (d.w1 12614 162) (d.w2 12614 162) := by
    positivity
  constructor
  · change (12614 : ℝ) ^ 8 * (mA 12614 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12614 162) (d.f1 12614 162) d.f2 + locationR16 12614 *
        radiusPolynomialRoot16 (d.f0 12614 162) (d.f1 12614 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12614 : ℝ) ^ 8 * (mA 12614 : ℝ) ^ 8 *
        ((((4661217349 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4661217349 / 1000000000000000000)) * ((1555061041 / 1000000000000000000)) * (126 / 100) +
          2 * (((1555061041 / 1000000000000000000)) ^ 2 + 2 * ((4661217349 / 1000000000000000000)) * ((373759491 / 1000000000000000000))) +
          6 * ((1555061041 / 1000000000000000000)) * ((373759491 / 1000000000000000000)) * (126 / 100) + 8 * ((373759491 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12614) *
          (32 * (((4661217349 / 1000000000000000000) : ℝ) + (1555061041 / 1000000000000000000) + (373759491 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12614 : ℝ) ^ 16 *
      (d.w0 12614 162 + d.w1 12614 162 * √(π / 2) + 2 * d.w2 12614 162 +
        energyR16 12614 * radiusPolynomialRoot16 (d.w0 12614 162) (d.w1 12614 162)
          (d.w2 12614 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12614 : ℝ) ^ 16 *
        (((187095283 / 10000000000000000000) : ℝ) + ((665573597 / 50000000000000000000)) * (126 / 100) + 2 * ((48636787 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12614) *
          (32 * (((187095283 / 10000000000000000000) : ℝ) + (665573597 / 50000000000000000000) + (48636787 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12614

/-! A coarse bound on the actual paper statistics constant at dimension 12615. -/
namespace BstLean.Part266.Row12615
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12613 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12613 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12613 128 ≤ (12867 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12867 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12615) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12615 : ℕ))
    (by norm_num : (12615 : ℕ) ≤ 16384)
  have ht : paperTail256 12615 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12615 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12615 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12615 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12615 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12615 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12613 128 * √(2 / (12615 : ℝ)) *
      (√(12615 : ℝ) + paperT0 12615 + paperTail256 12615) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12615 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12615 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12615 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12613 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12613 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12615 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12615

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12615
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12615 (61 / 100) 162 (17 / (100 * 12615)) (26 / (10 * 12615)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12615 (61 / 100) 162 (17 / (100 * 12615)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (19449879 / 4000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1541805731 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (675025503 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12615 / 12615 * (61 / 100)) ^ 4 * inverseRadius8 (12615 - 1) /
            envelopeGap 12615 (61 / 100) 162 (17 / (100 * 12615)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12615

namespace BstLean.Part266.Row12615
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12615 162 ≤ (4660295401 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12615 162 ≤ (1554753279 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (37368547 / 100000000000000000)
  w0 : (tableEnvelope C).w0 12615 162 ≤ (1870508277 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12615 162 ≤ (1330830817 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12615 162 ≤ (486252207 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (19449879 / 4000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (19449879 / 4000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1541805731 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (675025503 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3670969 / 1000000000) : ℝ) ≤ √(17 / (100 * 12615) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12615) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2205100849 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1227057317 / 31250000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12615) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12615) ≤ (112105713 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12615) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12615 * (162 : ℝ) ^ 2 + 26 / (10 * 12615) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12615) : ℝ)) (tA 12615 * 162 ^ 2 + 26 / (10 * 12615)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3670969 / 1000000000))) * ((19449879 / 4000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3670969 / 1000000000)) ^ 3) * ((1541805731 / 1000000000000000000000000))) + ((675025503 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3670969 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12615) : ℝ)) d.D d.V d.P (√(tA 12615) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3670969 / 1000000000)) ^ 2 * (((2205100849 / 1000000000000000)) * ((1227057317 / 31250000000000000)))) + ((675025503 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12615) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3670969 / 1000000000)) * ((19449879 / 4000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12615) : ℝ)) (tA 12615 * 162 ^ 2 + 26 / (10 * 12615)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((19449879 / 4000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3670969 / 1000000000)) ^ 2) * ((1541805731 / 1000000000000000000000000)) + ((675025503 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12615) : ℝ)) (√(26 / (10 * 12615) : ℝ)) d.D d.V d.P (√(tA 12615) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3670969 / 1000000000)) * (((2205100849 / 1000000000000000)) * ((1227057317 / 31250000000000000))) + ((675025503 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12615) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((19449879 / 4000000000000000000) : ℝ) + ((675025503 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12615

namespace BstLean.Part266.Row12615
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12615 162 ∧
    0 ≤ (tableEnvelope C).f1 12615 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12615 162 ∧
    0 ≤ (tableEnvelope C).w1 12615 162 ∧ 0 ≤ (tableEnvelope C).w2 12615 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12615 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12615 162 ∧ 0 ≤ d.f1 12615 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12615 162 ∧ 0 ≤ d.w1 12615 162 ∧ 0 ≤ d.w2 12615 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12615 ≤ 2 * (228 / 100 : ℝ) / 12615 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12615 ≤ 2 * (370 / 100 : ℝ) / 12615 := by
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
    (completeRAData (tableEnvelope C) 12615 162).locationBound 12615 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12615 162).energyBound 12615 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12615 162) (d.f1 12615 162) d.f2 ≤
      32 * (((4660295401 / 1000000000000000000) : ℝ) + (1554753279 / 1000000000000000000) + (37368547 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12615 162) (d.w1 12615 162)
      (d.w2 12615 162) ≤
      32 * (((1870508277 / 100000000000000000000) : ℝ) + (1330830817 / 100000000000000000000) + (486252207 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12615 162) (d.f1 12615 162) d.f2 ≤
      ((4660295401 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4660295401 / 1000000000000000000)) * ((1554753279 / 1000000000000000000)) * (126 / 100) +
      2 * (((1554753279 / 1000000000000000000)) ^ 2 + 2 * ((4660295401 / 1000000000000000000)) * ((37368547 / 100000000000000000))) +
      6 * ((1554753279 / 1000000000000000000)) * ((37368547 / 100000000000000000)) * (126 / 100) + 8 * ((37368547 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12615 162) (d.f1 12615 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12615 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12615 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12615 162) (d.f1 12615 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12615 162) (d.w1 12615 162) (d.w2 12615 162)
  have hwexpr0 : 0 ≤ d.w0 12615 162 + d.w1 12615 162 * √(π / 2) +
      2 * d.w2 12615 162 + energyR16 12615 *
      radiusPolynomialRoot16 (d.w0 12615 162) (d.w1 12615 162) (d.w2 12615 162) := by
    positivity
  constructor
  · change (12615 : ℝ) ^ 8 * (mA 12615 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12615 162) (d.f1 12615 162) d.f2 + locationR16 12615 *
        radiusPolynomialRoot16 (d.f0 12615 162) (d.f1 12615 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12615 : ℝ) ^ 8 * (mA 12615 : ℝ) ^ 8 *
        ((((4660295401 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4660295401 / 1000000000000000000)) * ((1554753279 / 1000000000000000000)) * (126 / 100) +
          2 * (((1554753279 / 1000000000000000000)) ^ 2 + 2 * ((4660295401 / 1000000000000000000)) * ((37368547 / 100000000000000000))) +
          6 * ((1554753279 / 1000000000000000000)) * ((37368547 / 100000000000000000)) * (126 / 100) + 8 * ((37368547 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12615) *
          (32 * (((4660295401 / 1000000000000000000) : ℝ) + (1554753279 / 1000000000000000000) + (37368547 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12615 : ℝ) ^ 16 *
      (d.w0 12615 162 + d.w1 12615 162 * √(π / 2) + 2 * d.w2 12615 162 +
        energyR16 12615 * radiusPolynomialRoot16 (d.w0 12615 162) (d.w1 12615 162)
          (d.w2 12615 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12615 : ℝ) ^ 16 *
        (((1870508277 / 100000000000000000000) : ℝ) + ((1330830817 / 100000000000000000000)) * (126 / 100) + 2 * ((486252207 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12615) *
          (32 * (((1870508277 / 100000000000000000000) : ℝ) + (1330830817 / 100000000000000000000) + (486252207 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12615

/-! A coarse bound on the actual paper statistics constant at dimension 12616. -/
namespace BstLean.Part266.Row12616
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12614 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12614 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12614 128 ≤ (12868 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12868 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12616) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12616 : ℕ))
    (by norm_num : (12616 : ℕ) ≤ 16384)
  have ht : paperTail256 12616 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12616 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12616 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12616 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12616 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12616 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12614 128 * √(2 / (12616 : ℝ)) *
      (√(12616 : ℝ) + paperT0 12616 + paperTail256 12616) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12616 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12616 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12616 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12614 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12614 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12616 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12616

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12616
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12616 (61 / 100) 162 (17 / (100 * 12616)) (26 / (10 * 12616)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12616 (61 / 100) 162 (17 / (100 * 12616)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (60766419 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (24083077 / 15625000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1079349449 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12616 / 12616 * (61 / 100)) ^ 4 * inverseRadius8 (12616 - 1) /
            envelopeGap 12616 (61 / 100) 162 (17 / (100 * 12616)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12616

namespace BstLean.Part266.Row12616
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12616 162 ≤ (2329685053 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12616 162 ≤ (1554444769 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (37361137 / 100000000000000000)
  w0 : (tableEnvelope C).w0 12616 162 ≤ (1870063123 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12616 162 ≤ (166314273 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 12616 162 ≤ (24306829 / 5000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (60766419 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (60766419 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (24083077 / 15625000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1079349449 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((458853 / 125000000) : ℝ) ≤ √(17 / (100 * 12616) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12616) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2204838661 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9814902343 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12616) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12616) ≤ (112096827 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12616) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12616 * (162 : ℝ) ^ 2 + 26 / (10 * 12616) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12616) : ℝ)) (tA 12616 * 162 ^ 2 + 26 / (10 * 12616)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((458853 / 125000000))) * ((60766419 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((458853 / 125000000)) ^ 3) * ((24083077 / 15625000000000000000000))) + ((1079349449 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((458853 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12616) : ℝ)) d.D d.V d.P (√(tA 12616) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((458853 / 125000000)) ^ 2 * (((2204838661 / 1000000000000000)) * ((9814902343 / 250000000000000000)))) + ((1079349449 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12616) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((458853 / 125000000)) * ((60766419 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12616) : ℝ)) (tA 12616 * 162 ^ 2 + 26 / (10 * 12616)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((60766419 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((458853 / 125000000)) ^ 2) * ((24083077 / 15625000000000000000000)) + ((1079349449 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12616) : ℝ)) (√(26 / (10 * 12616) : ℝ)) d.D d.V d.P (√(tA 12616) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((458853 / 125000000)) * (((2204838661 / 1000000000000000)) * ((9814902343 / 250000000000000000))) + ((1079349449 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12616) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((60766419 / 12500000000000000000) : ℝ) + ((1079349449 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12616

namespace BstLean.Part266.Row12616
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12616 162 ∧
    0 ≤ (tableEnvelope C).f1 12616 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12616 162 ∧
    0 ≤ (tableEnvelope C).w1 12616 162 ∧ 0 ≤ (tableEnvelope C).w2 12616 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12616 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12616 162 ∧ 0 ≤ d.f1 12616 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12616 162 ∧ 0 ≤ d.w1 12616 162 ∧ 0 ≤ d.w2 12616 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12616 ≤ 2 * (228 / 100 : ℝ) / 12616 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12616 ≤ 2 * (370 / 100 : ℝ) / 12616 := by
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
    (completeRAData (tableEnvelope C) 12616 162).locationBound 12616 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12616 162).energyBound 12616 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12616 162) (d.f1 12616 162) d.f2 ≤
      32 * (((2329685053 / 500000000000000000) : ℝ) + (1554444769 / 1000000000000000000) + (37361137 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12616 162) (d.w1 12616 162)
      (d.w2 12616 162) ≤
      32 * (((1870063123 / 100000000000000000000) : ℝ) + (166314273 / 12500000000000000000) + (24306829 / 5000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12616 162) (d.f1 12616 162) d.f2 ≤
      ((2329685053 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2329685053 / 500000000000000000)) * ((1554444769 / 1000000000000000000)) * (126 / 100) +
      2 * (((1554444769 / 1000000000000000000)) ^ 2 + 2 * ((2329685053 / 500000000000000000)) * ((37361137 / 100000000000000000))) +
      6 * ((1554444769 / 1000000000000000000)) * ((37361137 / 100000000000000000)) * (126 / 100) + 8 * ((37361137 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12616 162) (d.f1 12616 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12616 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12616 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12616 162) (d.f1 12616 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12616 162) (d.w1 12616 162) (d.w2 12616 162)
  have hwexpr0 : 0 ≤ d.w0 12616 162 + d.w1 12616 162 * √(π / 2) +
      2 * d.w2 12616 162 + energyR16 12616 *
      radiusPolynomialRoot16 (d.w0 12616 162) (d.w1 12616 162) (d.w2 12616 162) := by
    positivity
  constructor
  · change (12616 : ℝ) ^ 8 * (mA 12616 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12616 162) (d.f1 12616 162) d.f2 + locationR16 12616 *
        radiusPolynomialRoot16 (d.f0 12616 162) (d.f1 12616 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12616 : ℝ) ^ 8 * (mA 12616 : ℝ) ^ 8 *
        ((((2329685053 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2329685053 / 500000000000000000)) * ((1554444769 / 1000000000000000000)) * (126 / 100) +
          2 * (((1554444769 / 1000000000000000000)) ^ 2 + 2 * ((2329685053 / 500000000000000000)) * ((37361137 / 100000000000000000))) +
          6 * ((1554444769 / 1000000000000000000)) * ((37361137 / 100000000000000000)) * (126 / 100) + 8 * ((37361137 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12616) *
          (32 * (((2329685053 / 500000000000000000) : ℝ) + (1554444769 / 1000000000000000000) + (37361137 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12616 : ℝ) ^ 16 *
      (d.w0 12616 162 + d.w1 12616 162 * √(π / 2) + 2 * d.w2 12616 162 +
        energyR16 12616 * radiusPolynomialRoot16 (d.w0 12616 162) (d.w1 12616 162)
          (d.w2 12616 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12616 : ℝ) ^ 16 *
        (((1870063123 / 100000000000000000000) : ℝ) + ((166314273 / 12500000000000000000)) * (126 / 100) + 2 * ((24306829 / 5000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12616) *
          (32 * (((1870063123 / 100000000000000000000) : ℝ) + (166314273 / 12500000000000000000) + (24306829 / 5000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12616

/-! A coarse bound on the actual paper statistics constant at dimension 12617. -/
namespace BstLean.Part266.Row12617
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12615 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12615 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12615 128 ≤ (12869 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12869 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12617) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12617 : ℕ))
    (by norm_num : (12617 : ℕ) ≤ 16384)
  have ht : paperTail256 12617 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12617 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12617 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12617 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12617 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12617 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12615 128 * √(2 / (12617 : ℝ)) *
      (√(12617 : ℝ) + paperT0 12617 + paperTail256 12617) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12617 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12617 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12617 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12615 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12615 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12617 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12617

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12617
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12617 (61 / 100) 162 (17 / (100 * 12617)) (26 / (10 * 12617)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12617 (61 / 100) 162 (17 / (100 * 12617)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (97203153 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1540828319 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5393292959 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12617 / 12617 * (61 / 100)) ^ 4 * inverseRadius8 (12617 - 1) /
            envelopeGap 12617 (61 / 100) 162 (17 / (100 * 12617)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12617

namespace BstLean.Part266.Row12617
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12617 162 ≤ (1164611283 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12617 162 ≤ (1554136359 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (373537291 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12617 162 ≤ (1869618123 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12617 162 ≤ (1330197657 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12617 162 ≤ (48602099 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (97203153 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (97203153 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1540828319 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5393292959 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3670679 / 1000000000) : ℝ) ≤ √(17 / (100 * 12617) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12617) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (551144131 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9813346521 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12617) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12617) ≤ (56043971 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12617) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12617 * (162 : ℝ) ^ 2 + 26 / (10 * 12617) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12617) : ℝ)) (tA 12617 * 162 ^ 2 + 26 / (10 * 12617)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3670679 / 1000000000))) * ((97203153 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3670679 / 1000000000)) ^ 3) * ((1540828319 / 1000000000000000000000000))) + ((5393292959 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3670679 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12617) : ℝ)) d.D d.V d.P (√(tA 12617) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3670679 / 1000000000)) ^ 2 * (((551144131 / 250000000000000)) * ((9813346521 / 250000000000000000)))) + ((5393292959 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12617) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3670679 / 1000000000)) * ((97203153 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12617) : ℝ)) (tA 12617 * 162 ^ 2 + 26 / (10 * 12617)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((97203153 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3670679 / 1000000000)) ^ 2) * ((1540828319 / 1000000000000000000000000)) + ((5393292959 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12617) : ℝ)) (√(26 / (10 * 12617) : ℝ)) d.D d.V d.P (√(tA 12617) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3670679 / 1000000000)) * (((551144131 / 250000000000000)) * ((9813346521 / 250000000000000000))) + ((5393292959 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12617) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((97203153 / 20000000000000000000) : ℝ) + ((5393292959 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12617

namespace BstLean.Part266.Row12617
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12617 162 ∧
    0 ≤ (tableEnvelope C).f1 12617 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12617 162 ∧
    0 ≤ (tableEnvelope C).w1 12617 162 ∧ 0 ≤ (tableEnvelope C).w2 12617 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12617 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12617 162 ∧ 0 ≤ d.f1 12617 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12617 162 ∧ 0 ≤ d.w1 12617 162 ∧ 0 ≤ d.w2 12617 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12617 ≤ 2 * (228 / 100 : ℝ) / 12617 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12617 ≤ 2 * (370 / 100 : ℝ) / 12617 := by
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
    (completeRAData (tableEnvelope C) 12617 162).locationBound 12617 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12617 162).energyBound 12617 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12617 162) (d.f1 12617 162) d.f2 ≤
      32 * (((1164611283 / 250000000000000000) : ℝ) + (1554136359 / 1000000000000000000) + (373537291 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12617 162) (d.w1 12617 162)
      (d.w2 12617 162) ≤
      32 * (((1869618123 / 100000000000000000000) : ℝ) + (1330197657 / 100000000000000000000) + (48602099 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12617 162) (d.f1 12617 162) d.f2 ≤
      ((1164611283 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1164611283 / 250000000000000000)) * ((1554136359 / 1000000000000000000)) * (126 / 100) +
      2 * (((1554136359 / 1000000000000000000)) ^ 2 + 2 * ((1164611283 / 250000000000000000)) * ((373537291 / 1000000000000000000))) +
      6 * ((1554136359 / 1000000000000000000)) * ((373537291 / 1000000000000000000)) * (126 / 100) + 8 * ((373537291 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12617 162) (d.f1 12617 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12617 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12617 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12617 162) (d.f1 12617 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12617 162) (d.w1 12617 162) (d.w2 12617 162)
  have hwexpr0 : 0 ≤ d.w0 12617 162 + d.w1 12617 162 * √(π / 2) +
      2 * d.w2 12617 162 + energyR16 12617 *
      radiusPolynomialRoot16 (d.w0 12617 162) (d.w1 12617 162) (d.w2 12617 162) := by
    positivity
  constructor
  · change (12617 : ℝ) ^ 8 * (mA 12617 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12617 162) (d.f1 12617 162) d.f2 + locationR16 12617 *
        radiusPolynomialRoot16 (d.f0 12617 162) (d.f1 12617 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12617 : ℝ) ^ 8 * (mA 12617 : ℝ) ^ 8 *
        ((((1164611283 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1164611283 / 250000000000000000)) * ((1554136359 / 1000000000000000000)) * (126 / 100) +
          2 * (((1554136359 / 1000000000000000000)) ^ 2 + 2 * ((1164611283 / 250000000000000000)) * ((373537291 / 1000000000000000000))) +
          6 * ((1554136359 / 1000000000000000000)) * ((373537291 / 1000000000000000000)) * (126 / 100) + 8 * ((373537291 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12617) *
          (32 * (((1164611283 / 250000000000000000) : ℝ) + (1554136359 / 1000000000000000000) + (373537291 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12617 : ℝ) ^ 16 *
      (d.w0 12617 162 + d.w1 12617 162 * √(π / 2) + 2 * d.w2 12617 162 +
        energyR16 12617 * radiusPolynomialRoot16 (d.w0 12617 162) (d.w1 12617 162)
          (d.w2 12617 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12617 : ℝ) ^ 16 *
        (((1869618123 / 100000000000000000000) : ℝ) + ((1330197657 / 100000000000000000000)) * (126 / 100) + 2 * ((48602099 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12617) *
          (32 * (((1869618123 / 100000000000000000000) : ℝ) + (1330197657 / 100000000000000000000) + (48602099 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12617

/-! A coarse bound on the actual paper statistics constant at dimension 12618. -/
namespace BstLean.Part266.Row12618
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12616 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12616 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12616 128 ≤ (12870 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12870 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12618) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12618 : ℕ))
    (by norm_num : (12618 : ℕ) ≤ 16384)
  have ht : paperTail256 12618 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12618 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12618 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12618 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12618 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12618 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12616 128 * √(2 / (12618 : ℝ)) *
      (√(12618 : ℝ) + paperT0 12618 + paperTail256 12618) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12618 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12618 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12618 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12616 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12616 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12618 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12618

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12618
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12618 (61 / 100) 162 (17 / (100 * 12618)) (26 / (10 * 12618)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12618 (61 / 100) 162 (17 / (100 * 12618)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (97180043 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (24067811 / 15625000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2694920581 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12618 / 12618 * (61 / 100)) ^ 4 * inverseRadius8 (12618 - 1) /
            envelopeGap 12618 (61 / 100) 162 (17 / (100 * 12618)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12618

namespace BstLean.Part266.Row12618
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12618 162 ≤ (2328762071 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12618 162 ≤ (1553828897 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (373463337 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12618 162 ≤ (1869174031 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12618 162 ≤ (103897 / 7812500000000000)
  w2 : (tableEnvelope C).w2 12618 162 ≤ (485905437 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (97180043 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (97180043 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (24067811 / 15625000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2694920581 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3670533 / 1000000000) : ℝ) ≤ √(17 / (100 * 12618) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12618) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (55107861 / 25000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (981179107 / 25000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12618) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12618) ≤ (112079059 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12618) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12618 * (162 : ℝ) ^ 2 + 26 / (10 * 12618) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12618) : ℝ)) (tA 12618 * 162 ^ 2 + 26 / (10 * 12618)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3670533 / 1000000000))) * ((97180043 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3670533 / 1000000000)) ^ 3) * ((24067811 / 15625000000000000000000))) + ((2694920581 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3670533 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12618) : ℝ)) d.D d.V d.P (√(tA 12618) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3670533 / 1000000000)) ^ 2 * (((55107861 / 25000000000000)) * ((981179107 / 25000000000000000)))) + ((2694920581 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12618) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3670533 / 1000000000)) * ((97180043 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12618) : ℝ)) (tA 12618 * 162 ^ 2 + 26 / (10 * 12618)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((97180043 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3670533 / 1000000000)) ^ 2) * ((24067811 / 15625000000000000000000)) + ((2694920581 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12618) : ℝ)) (√(26 / (10 * 12618) : ℝ)) d.D d.V d.P (√(tA 12618) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3670533 / 1000000000)) * (((55107861 / 25000000000000)) * ((981179107 / 25000000000000000))) + ((2694920581 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12618) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((97180043 / 20000000000000000000) : ℝ) + ((2694920581 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12618

namespace BstLean.Part266.Row12618
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12618 162 ∧
    0 ≤ (tableEnvelope C).f1 12618 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12618 162 ∧
    0 ≤ (tableEnvelope C).w1 12618 162 ∧ 0 ≤ (tableEnvelope C).w2 12618 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12618 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12618 162 ∧ 0 ≤ d.f1 12618 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12618 162 ∧ 0 ≤ d.w1 12618 162 ∧ 0 ≤ d.w2 12618 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12618 ≤ 2 * (228 / 100 : ℝ) / 12618 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12618 ≤ 2 * (370 / 100 : ℝ) / 12618 := by
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
    (completeRAData (tableEnvelope C) 12618 162).locationBound 12618 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12618 162).energyBound 12618 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12618 162) (d.f1 12618 162) d.f2 ≤
      32 * (((2328762071 / 500000000000000000) : ℝ) + (1553828897 / 1000000000000000000) + (373463337 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12618 162) (d.w1 12618 162)
      (d.w2 12618 162) ≤
      32 * (((1869174031 / 100000000000000000000) : ℝ) + (103897 / 7812500000000000) + (485905437 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12618 162) (d.f1 12618 162) d.f2 ≤
      ((2328762071 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2328762071 / 500000000000000000)) * ((1553828897 / 1000000000000000000)) * (126 / 100) +
      2 * (((1553828897 / 1000000000000000000)) ^ 2 + 2 * ((2328762071 / 500000000000000000)) * ((373463337 / 1000000000000000000))) +
      6 * ((1553828897 / 1000000000000000000)) * ((373463337 / 1000000000000000000)) * (126 / 100) + 8 * ((373463337 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12618 162) (d.f1 12618 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12618 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12618 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12618 162) (d.f1 12618 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12618 162) (d.w1 12618 162) (d.w2 12618 162)
  have hwexpr0 : 0 ≤ d.w0 12618 162 + d.w1 12618 162 * √(π / 2) +
      2 * d.w2 12618 162 + energyR16 12618 *
      radiusPolynomialRoot16 (d.w0 12618 162) (d.w1 12618 162) (d.w2 12618 162) := by
    positivity
  constructor
  · change (12618 : ℝ) ^ 8 * (mA 12618 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12618 162) (d.f1 12618 162) d.f2 + locationR16 12618 *
        radiusPolynomialRoot16 (d.f0 12618 162) (d.f1 12618 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12618 : ℝ) ^ 8 * (mA 12618 : ℝ) ^ 8 *
        ((((2328762071 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2328762071 / 500000000000000000)) * ((1553828897 / 1000000000000000000)) * (126 / 100) +
          2 * (((1553828897 / 1000000000000000000)) ^ 2 + 2 * ((2328762071 / 500000000000000000)) * ((373463337 / 1000000000000000000))) +
          6 * ((1553828897 / 1000000000000000000)) * ((373463337 / 1000000000000000000)) * (126 / 100) + 8 * ((373463337 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12618) *
          (32 * (((2328762071 / 500000000000000000) : ℝ) + (1553828897 / 1000000000000000000) + (373463337 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12618 : ℝ) ^ 16 *
      (d.w0 12618 162 + d.w1 12618 162 * √(π / 2) + 2 * d.w2 12618 162 +
        energyR16 12618 * radiusPolynomialRoot16 (d.w0 12618 162) (d.w1 12618 162)
          (d.w2 12618 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12618 : ℝ) ^ 16 *
        (((1869174031 / 100000000000000000000) : ℝ) + ((103897 / 7812500000000000)) * (126 / 100) + 2 * ((485905437 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12618) *
          (32 * (((1869174031 / 100000000000000000000) : ℝ) + (103897 / 7812500000000000) + (485905437 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12618

/-! A coarse bound on the actual paper statistics constant at dimension 12619. -/
namespace BstLean.Part266.Row12619
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12617 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12617 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12617 128 ≤ (12871 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12871 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12619) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12619 : ℕ))
    (by norm_num : (12619 : ℕ) ≤ 16384)
  have ht : paperTail256 12619 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12619 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12619 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12619 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12619 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12619 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12617 128 * √(2 / (12619 : ℝ)) *
      (√(12619 : ℝ) + paperT0 12619 + paperTail256 12619) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12619 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12619 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12619 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12617 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12617 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12619 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12619

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12619
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12619 (61 / 100) 162 (17 / (100 * 12619)) (26 / (10 * 12619)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12619 (61 / 100) 162 (17 / (100 * 12619)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (242892351 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (769925841 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1346597963 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12619 / 12619 * (61 / 100)) ^ 4 * inverseRadius8 (12619 - 1) /
            envelopeGap 12619 (61 / 100) 162 (17 / (100 * 12619)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12619

namespace BstLean.Part266.Row12619
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12619 162 ≤ (18189843 / 3906250000000000)
  f1 : (tableEnvelope C).f1 12619 162 ≤ (1553520689 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (46673663 / 125000000000000000)
  w0 : (tableEnvelope C).w0 12619 162 ≤ (93436467 / 5000000000000000000)
  w1 : (tableEnvelope C).w1 12619 162 ≤ (1329565287 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12619 162 ≤ (3036187 / 625000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (242892351 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (242892351 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (769925841 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1346597963 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((917597 / 250000000) : ℝ) ≤ √(17 / (100 * 12619) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12619) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2204052409 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39240943949 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12619) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12619) ≤ (112070177 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12619) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12619 * (162 : ℝ) ^ 2 + 26 / (10 * 12619) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12619) : ℝ)) (tA 12619 * 162 ^ 2 + 26 / (10 * 12619)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((917597 / 250000000))) * ((242892351 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((917597 / 250000000)) ^ 3) * ((769925841 / 500000000000000000000000))) + ((1346597963 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((917597 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12619) : ℝ)) d.D d.V d.P (√(tA 12619) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((917597 / 250000000)) ^ 2 * (((2204052409 / 1000000000000000)) * ((39240943949 / 1000000000000000000)))) + ((1346597963 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12619) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((917597 / 250000000)) * ((242892351 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12619) : ℝ)) (tA 12619 * 162 ^ 2 + 26 / (10 * 12619)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((242892351 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((917597 / 250000000)) ^ 2) * ((769925841 / 500000000000000000000000)) + ((1346597963 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12619) : ℝ)) (√(26 / (10 * 12619) : ℝ)) d.D d.V d.P (√(tA 12619) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((917597 / 250000000)) * (((2204052409 / 1000000000000000)) * ((39240943949 / 1000000000000000000))) + ((1346597963 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12619) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((242892351 / 50000000000000000000) : ℝ) + ((1346597963 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12619

namespace BstLean.Part266.Row12619
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12619 162 ∧
    0 ≤ (tableEnvelope C).f1 12619 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12619 162 ∧
    0 ≤ (tableEnvelope C).w1 12619 162 ∧ 0 ≤ (tableEnvelope C).w2 12619 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12619 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12619 162 ∧ 0 ≤ d.f1 12619 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12619 162 ∧ 0 ≤ d.w1 12619 162 ∧ 0 ≤ d.w2 12619 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12619 ≤ 2 * (228 / 100 : ℝ) / 12619 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12619 ≤ 2 * (370 / 100 : ℝ) / 12619 := by
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
    (completeRAData (tableEnvelope C) 12619 162).locationBound 12619 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12619 162).energyBound 12619 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12619 162) (d.f1 12619 162) d.f2 ≤
      32 * (((18189843 / 3906250000000000) : ℝ) + (1553520689 / 1000000000000000000) + (46673663 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12619 162) (d.w1 12619 162)
      (d.w2 12619 162) ≤
      32 * (((93436467 / 5000000000000000000) : ℝ) + (1329565287 / 100000000000000000000) + (3036187 / 625000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12619 162) (d.f1 12619 162) d.f2 ≤
      ((18189843 / 3906250000000000) : ℝ) ^ 2 + 2 * ((18189843 / 3906250000000000)) * ((1553520689 / 1000000000000000000)) * (126 / 100) +
      2 * (((1553520689 / 1000000000000000000)) ^ 2 + 2 * ((18189843 / 3906250000000000)) * ((46673663 / 125000000000000000))) +
      6 * ((1553520689 / 1000000000000000000)) * ((46673663 / 125000000000000000)) * (126 / 100) + 8 * ((46673663 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12619 162) (d.f1 12619 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12619 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12619 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12619 162) (d.f1 12619 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12619 162) (d.w1 12619 162) (d.w2 12619 162)
  have hwexpr0 : 0 ≤ d.w0 12619 162 + d.w1 12619 162 * √(π / 2) +
      2 * d.w2 12619 162 + energyR16 12619 *
      radiusPolynomialRoot16 (d.w0 12619 162) (d.w1 12619 162) (d.w2 12619 162) := by
    positivity
  constructor
  · change (12619 : ℝ) ^ 8 * (mA 12619 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12619 162) (d.f1 12619 162) d.f2 + locationR16 12619 *
        radiusPolynomialRoot16 (d.f0 12619 162) (d.f1 12619 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12619 : ℝ) ^ 8 * (mA 12619 : ℝ) ^ 8 *
        ((((18189843 / 3906250000000000) : ℝ) ^ 2 + 2 * ((18189843 / 3906250000000000)) * ((1553520689 / 1000000000000000000)) * (126 / 100) +
          2 * (((1553520689 / 1000000000000000000)) ^ 2 + 2 * ((18189843 / 3906250000000000)) * ((46673663 / 125000000000000000))) +
          6 * ((1553520689 / 1000000000000000000)) * ((46673663 / 125000000000000000)) * (126 / 100) + 8 * ((46673663 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12619) *
          (32 * (((18189843 / 3906250000000000) : ℝ) + (1553520689 / 1000000000000000000) + (46673663 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12619 : ℝ) ^ 16 *
      (d.w0 12619 162 + d.w1 12619 162 * √(π / 2) + 2 * d.w2 12619 162 +
        energyR16 12619 * radiusPolynomialRoot16 (d.w0 12619 162) (d.w1 12619 162)
          (d.w2 12619 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12619 : ℝ) ^ 16 *
        (((93436467 / 5000000000000000000) : ℝ) + ((1329565287 / 100000000000000000000)) * (126 / 100) + 2 * ((3036187 / 625000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12619) *
          (32 * (((93436467 / 5000000000000000000) : ℝ) + (1329565287 / 100000000000000000000) + (3036187 / 625000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12619

/-! A coarse bound on the actual paper statistics constant at dimension 12620. -/
namespace BstLean.Part266.Row12620
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12618 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12618 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12618 128 ≤ (12872 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12872 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12620) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12620 : ℕ))
    (by norm_num : (12620 : ℕ) ≤ 16384)
  have ht : paperTail256 12620 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12620 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12620 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12620 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12620 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12620 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12618 128 * √(2 / (12620 : ℝ)) *
      (√(12620 : ℝ) + paperT0 12620 + paperTail256 12620) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12620 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12620 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12620 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12618 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12618 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12620 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12620

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12620
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12620 (61 / 100) 162 (17 / (100 * 12620)) (26 / (10 * 12620)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12620 (61 / 100) 162 (17 / (100 * 12620)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (242834613 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1539363653 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5382945029 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12620 / 12620 * (61 / 100)) ^ 4 * inverseRadius8 (12620 - 1) /
            envelopeGap 12620 (61 / 100) 162 (17 / (100 * 12620)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12620

namespace BstLean.Part266.Row12620
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12620 162 ≤ (4655679453 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12620 162 ≤ (388303357 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (93328849 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12620 162 ≤ (467071389 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12620 162 ≤ (332312361 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12620 162 ≤ (485674441 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (242834613 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (242834613 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1539363653 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5382945029 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1835121 / 500000000) : ℝ) ≤ √(17 / (100 * 12620) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12620) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2203790431 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9808681273 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12620) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12620) ≤ (112061297 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12620) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12620 * (162 : ℝ) ^ 2 + 26 / (10 * 12620) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12620) : ℝ)) (tA 12620 * 162 ^ 2 + 26 / (10 * 12620)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1835121 / 500000000))) * ((242834613 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1835121 / 500000000)) ^ 3) * ((1539363653 / 1000000000000000000000000))) + ((5382945029 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1835121 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12620) : ℝ)) d.D d.V d.P (√(tA 12620) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1835121 / 500000000)) ^ 2 * (((2203790431 / 1000000000000000)) * ((9808681273 / 250000000000000000)))) + ((5382945029 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12620) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1835121 / 500000000)) * ((242834613 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12620) : ℝ)) (tA 12620 * 162 ^ 2 + 26 / (10 * 12620)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((242834613 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1835121 / 500000000)) ^ 2) * ((1539363653 / 1000000000000000000000000)) + ((5382945029 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12620) : ℝ)) (√(26 / (10 * 12620) : ℝ)) d.D d.V d.P (√(tA 12620) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1835121 / 500000000)) * (((2203790431 / 1000000000000000)) * ((9808681273 / 250000000000000000))) + ((5382945029 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12620) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((242834613 / 50000000000000000000) : ℝ) + ((5382945029 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12620

namespace BstLean.Part266.Row12620
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12620 162 ∧
    0 ≤ (tableEnvelope C).f1 12620 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12620 162 ∧
    0 ≤ (tableEnvelope C).w1 12620 162 ∧ 0 ≤ (tableEnvelope C).w2 12620 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12620 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12620 162 ∧ 0 ≤ d.f1 12620 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12620 162 ∧ 0 ≤ d.w1 12620 162 ∧ 0 ≤ d.w2 12620 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12620 ≤ 2 * (228 / 100 : ℝ) / 12620 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12620 ≤ 2 * (370 / 100 : ℝ) / 12620 := by
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
    (completeRAData (tableEnvelope C) 12620 162).locationBound 12620 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12620 162).energyBound 12620 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12620 162) (d.f1 12620 162) d.f2 ≤
      32 * (((4655679453 / 1000000000000000000) : ℝ) + (388303357 / 250000000000000000) + (93328849 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12620 162) (d.w1 12620 162)
      (d.w2 12620 162) ≤
      32 * (((467071389 / 25000000000000000000) : ℝ) + (332312361 / 25000000000000000000) + (485674441 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12620 162) (d.f1 12620 162) d.f2 ≤
      ((4655679453 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4655679453 / 1000000000000000000)) * ((388303357 / 250000000000000000)) * (126 / 100) +
      2 * (((388303357 / 250000000000000000)) ^ 2 + 2 * ((4655679453 / 1000000000000000000)) * ((93328849 / 250000000000000000))) +
      6 * ((388303357 / 250000000000000000)) * ((93328849 / 250000000000000000)) * (126 / 100) + 8 * ((93328849 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12620 162) (d.f1 12620 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12620 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12620 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12620 162) (d.f1 12620 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12620 162) (d.w1 12620 162) (d.w2 12620 162)
  have hwexpr0 : 0 ≤ d.w0 12620 162 + d.w1 12620 162 * √(π / 2) +
      2 * d.w2 12620 162 + energyR16 12620 *
      radiusPolynomialRoot16 (d.w0 12620 162) (d.w1 12620 162) (d.w2 12620 162) := by
    positivity
  constructor
  · change (12620 : ℝ) ^ 8 * (mA 12620 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12620 162) (d.f1 12620 162) d.f2 + locationR16 12620 *
        radiusPolynomialRoot16 (d.f0 12620 162) (d.f1 12620 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12620 : ℝ) ^ 8 * (mA 12620 : ℝ) ^ 8 *
        ((((4655679453 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4655679453 / 1000000000000000000)) * ((388303357 / 250000000000000000)) * (126 / 100) +
          2 * (((388303357 / 250000000000000000)) ^ 2 + 2 * ((4655679453 / 1000000000000000000)) * ((93328849 / 250000000000000000))) +
          6 * ((388303357 / 250000000000000000)) * ((93328849 / 250000000000000000)) * (126 / 100) + 8 * ((93328849 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12620) *
          (32 * (((4655679453 / 1000000000000000000) : ℝ) + (388303357 / 250000000000000000) + (93328849 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12620 : ℝ) ^ 16 *
      (d.w0 12620 162 + d.w1 12620 162 * √(π / 2) + 2 * d.w2 12620 162 +
        energyR16 12620 * radiusPolynomialRoot16 (d.w0 12620 162) (d.w1 12620 162)
          (d.w2 12620 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12620 : ℝ) ^ 16 *
        (((467071389 / 25000000000000000000) : ℝ) + ((332312361 / 25000000000000000000)) * (126 / 100) + 2 * ((485674441 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12620) *
          (32 * (((467071389 / 25000000000000000000) : ℝ) + (332312361 / 25000000000000000000) + (485674441 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12620

/-! A coarse bound on the actual paper statistics constant at dimension 12621. -/
namespace BstLean.Part266.Row12621
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12619 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12619 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12619 128 ≤ (12873 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12873 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12621) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12621 : ℕ))
    (by norm_num : (12621 : ℕ) ≤ 16384)
  have ht : paperTail256 12621 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12621 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12621 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12621 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12621 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12621 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12619 128 * √(2 / (12621 : ℝ)) *
      (√(12621 : ℝ) + paperT0 12621 + paperTail256 12621) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12621 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12621 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12621 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12619 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12619 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12621 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12621

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12621
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12621 (61 / 100) 162 (17 / (100 * 12621)) (26 / (10 * 12621)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12621 (61 / 100) 162 (17 / (100 * 12621)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (97110757 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (769437909 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5379500689 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12621 / 12621 * (61 / 100)) ^ 4 * inverseRadius8 (12621 - 1) /
            envelopeGap 12621 (61 / 100) 162 (17 / (100 * 12621)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12621

namespace BstLean.Part266.Row12621
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12621 162 ≤ (4654755757 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12621 162 ≤ (1552905417 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (186620703 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12621 162 ≤ (466960293 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12621 162 ≤ (664466671 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12621 162 ≤ (485558997 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (97110757 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (97110757 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (769437909 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5379500689 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3670097 / 1000000000) : ℝ) ≤ √(17 / (100 * 12621) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12621) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (4407057 / 2000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39228507721 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12621) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12621) ≤ (56026209 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12621) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12621 * (162 : ℝ) ^ 2 + 26 / (10 * 12621) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12621) : ℝ)) (tA 12621 * 162 ^ 2 + 26 / (10 * 12621)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3670097 / 1000000000))) * ((97110757 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3670097 / 1000000000)) ^ 3) * ((769437909 / 500000000000000000000000))) + ((5379500689 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3670097 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12621) : ℝ)) d.D d.V d.P (√(tA 12621) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3670097 / 1000000000)) ^ 2 * (((4407057 / 2000000000000)) * ((39228507721 / 1000000000000000000)))) + ((5379500689 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12621) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3670097 / 1000000000)) * ((97110757 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12621) : ℝ)) (tA 12621 * 162 ^ 2 + 26 / (10 * 12621)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((97110757 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3670097 / 1000000000)) ^ 2) * ((769437909 / 500000000000000000000000)) + ((5379500689 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12621) : ℝ)) (√(26 / (10 * 12621) : ℝ)) d.D d.V d.P (√(tA 12621) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3670097 / 1000000000)) * (((4407057 / 2000000000000)) * ((39228507721 / 1000000000000000000))) + ((5379500689 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12621) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((97110757 / 20000000000000000000) : ℝ) + ((5379500689 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12621

namespace BstLean.Part266.Row12621
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12621 162 ∧
    0 ≤ (tableEnvelope C).f1 12621 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12621 162 ∧
    0 ≤ (tableEnvelope C).w1 12621 162 ∧ 0 ≤ (tableEnvelope C).w2 12621 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12621 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12621 162 ∧ 0 ≤ d.f1 12621 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12621 162 ∧ 0 ≤ d.w1 12621 162 ∧ 0 ≤ d.w2 12621 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12621 ≤ 2 * (228 / 100 : ℝ) / 12621 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12621 ≤ 2 * (370 / 100 : ℝ) / 12621 := by
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
    (completeRAData (tableEnvelope C) 12621 162).locationBound 12621 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12621 162).energyBound 12621 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12621 162) (d.f1 12621 162) d.f2 ≤
      32 * (((4654755757 / 1000000000000000000) : ℝ) + (1552905417 / 1000000000000000000) + (186620703 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12621 162) (d.w1 12621 162)
      (d.w2 12621 162) ≤
      32 * (((466960293 / 25000000000000000000) : ℝ) + (664466671 / 50000000000000000000) + (485558997 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12621 162) (d.f1 12621 162) d.f2 ≤
      ((4654755757 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4654755757 / 1000000000000000000)) * ((1552905417 / 1000000000000000000)) * (126 / 100) +
      2 * (((1552905417 / 1000000000000000000)) ^ 2 + 2 * ((4654755757 / 1000000000000000000)) * ((186620703 / 500000000000000000))) +
      6 * ((1552905417 / 1000000000000000000)) * ((186620703 / 500000000000000000)) * (126 / 100) + 8 * ((186620703 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12621 162) (d.f1 12621 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12621 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12621 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12621 162) (d.f1 12621 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12621 162) (d.w1 12621 162) (d.w2 12621 162)
  have hwexpr0 : 0 ≤ d.w0 12621 162 + d.w1 12621 162 * √(π / 2) +
      2 * d.w2 12621 162 + energyR16 12621 *
      radiusPolynomialRoot16 (d.w0 12621 162) (d.w1 12621 162) (d.w2 12621 162) := by
    positivity
  constructor
  · change (12621 : ℝ) ^ 8 * (mA 12621 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12621 162) (d.f1 12621 162) d.f2 + locationR16 12621 *
        radiusPolynomialRoot16 (d.f0 12621 162) (d.f1 12621 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12621 : ℝ) ^ 8 * (mA 12621 : ℝ) ^ 8 *
        ((((4654755757 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4654755757 / 1000000000000000000)) * ((1552905417 / 1000000000000000000)) * (126 / 100) +
          2 * (((1552905417 / 1000000000000000000)) ^ 2 + 2 * ((4654755757 / 1000000000000000000)) * ((186620703 / 500000000000000000))) +
          6 * ((1552905417 / 1000000000000000000)) * ((186620703 / 500000000000000000)) * (126 / 100) + 8 * ((186620703 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12621) *
          (32 * (((4654755757 / 1000000000000000000) : ℝ) + (1552905417 / 1000000000000000000) + (186620703 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12621 : ℝ) ^ 16 *
      (d.w0 12621 162 + d.w1 12621 162 * √(π / 2) + 2 * d.w2 12621 162 +
        energyR16 12621 * radiusPolynomialRoot16 (d.w0 12621 162) (d.w1 12621 162)
          (d.w2 12621 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12621 : ℝ) ^ 16 *
        (((466960293 / 25000000000000000000) : ℝ) + ((664466671 / 50000000000000000000)) * (126 / 100) + 2 * ((485558997 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12621) *
          (32 * (((466960293 / 25000000000000000000) : ℝ) + (664466671 / 50000000000000000000) + (485558997 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12621

/-! A coarse bound on the actual paper statistics constant at dimension 12622. -/
namespace BstLean.Part266.Row12622
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12620 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12620 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12620 128 ≤ (12874 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12874 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12622) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12622 : ℕ))
    (by norm_num : (12622 : ℕ) ≤ 16384)
  have ht : paperTail256 12622 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12622 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12622 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12622 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12622 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12622 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12620 128 * √(2 / (12622 : ℝ)) *
      (√(12622 : ℝ) + paperT0 12622 + paperTail256 12622) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12622 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12622 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12622 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12620 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12620 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12622 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12622

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12622
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12622 (61 / 100) 162 (17 / (100 * 12622)) (26 / (10 * 12622)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12622 (61 / 100) 162 (17 / (100 * 12622)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (242719191 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (96149261 / 62500000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (537605883 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12622 / 12622 * (61 / 100)) ^ 4 * inverseRadius8 (12622 - 1) /
            envelopeGap 12622 (61 / 100) 162 (17 / (100 * 12622)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12622

namespace BstLean.Part266.Row12622
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12622 162 ≤ (4653836041 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12622 162 ≤ (310519671 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (186583771 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12622 162 ≤ (29178089 / 1562500000000000000)
  w1 : (tableEnvelope C).w1 12622 162 ≤ (83038607 / 6250000000000000000)
  w2 : (tableEnvelope C).w2 12622 162 ≤ (48544359 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (242719191 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (242719191 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (96149261 / 62500000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (537605883 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3669951 / 1000000000) : ℝ) ≤ √(17 / (100 * 12622) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12622) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (17626133 / 8000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1568891673 / 40000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12622) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12622) ≤ (112043541 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12622) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12622 * (162 : ℝ) ^ 2 + 26 / (10 * 12622) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12622) : ℝ)) (tA 12622 * 162 ^ 2 + 26 / (10 * 12622)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3669951 / 1000000000))) * ((242719191 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3669951 / 1000000000)) ^ 3) * ((96149261 / 62500000000000000000000))) + ((537605883 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3669951 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12622) : ℝ)) d.D d.V d.P (√(tA 12622) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3669951 / 1000000000)) ^ 2 * (((17626133 / 8000000000000)) * ((1568891673 / 40000000000000000)))) + ((537605883 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12622) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3669951 / 1000000000)) * ((242719191 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12622) : ℝ)) (tA 12622 * 162 ^ 2 + 26 / (10 * 12622)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((242719191 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3669951 / 1000000000)) ^ 2) * ((96149261 / 62500000000000000000000)) + ((537605883 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12622) : ℝ)) (√(26 / (10 * 12622) : ℝ)) d.D d.V d.P (√(tA 12622) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3669951 / 1000000000)) * (((17626133 / 8000000000000)) * ((1568891673 / 40000000000000000))) + ((537605883 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12622) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((242719191 / 50000000000000000000) : ℝ) + ((537605883 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12622

namespace BstLean.Part266.Row12622
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12622 162 ∧
    0 ≤ (tableEnvelope C).f1 12622 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12622 162 ∧
    0 ≤ (tableEnvelope C).w1 12622 162 ∧ 0 ≤ (tableEnvelope C).w2 12622 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12622 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12622 162 ∧ 0 ≤ d.f1 12622 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12622 162 ∧ 0 ≤ d.w1 12622 162 ∧ 0 ≤ d.w2 12622 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12622 ≤ 2 * (228 / 100 : ℝ) / 12622 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12622 ≤ 2 * (370 / 100 : ℝ) / 12622 := by
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
    (completeRAData (tableEnvelope C) 12622 162).locationBound 12622 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12622 162).energyBound 12622 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12622 162) (d.f1 12622 162) d.f2 ≤
      32 * (((4653836041 / 1000000000000000000) : ℝ) + (310519671 / 200000000000000000) + (186583771 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12622 162) (d.w1 12622 162)
      (d.w2 12622 162) ≤
      32 * (((29178089 / 1562500000000000000) : ℝ) + (83038607 / 6250000000000000000) + (48544359 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12622 162) (d.f1 12622 162) d.f2 ≤
      ((4653836041 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4653836041 / 1000000000000000000)) * ((310519671 / 200000000000000000)) * (126 / 100) +
      2 * (((310519671 / 200000000000000000)) ^ 2 + 2 * ((4653836041 / 1000000000000000000)) * ((186583771 / 500000000000000000))) +
      6 * ((310519671 / 200000000000000000)) * ((186583771 / 500000000000000000)) * (126 / 100) + 8 * ((186583771 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12622 162) (d.f1 12622 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12622 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12622 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12622 162) (d.f1 12622 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12622 162) (d.w1 12622 162) (d.w2 12622 162)
  have hwexpr0 : 0 ≤ d.w0 12622 162 + d.w1 12622 162 * √(π / 2) +
      2 * d.w2 12622 162 + energyR16 12622 *
      radiusPolynomialRoot16 (d.w0 12622 162) (d.w1 12622 162) (d.w2 12622 162) := by
    positivity
  constructor
  · change (12622 : ℝ) ^ 8 * (mA 12622 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12622 162) (d.f1 12622 162) d.f2 + locationR16 12622 *
        radiusPolynomialRoot16 (d.f0 12622 162) (d.f1 12622 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12622 : ℝ) ^ 8 * (mA 12622 : ℝ) ^ 8 *
        ((((4653836041 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4653836041 / 1000000000000000000)) * ((310519671 / 200000000000000000)) * (126 / 100) +
          2 * (((310519671 / 200000000000000000)) ^ 2 + 2 * ((4653836041 / 1000000000000000000)) * ((186583771 / 500000000000000000))) +
          6 * ((310519671 / 200000000000000000)) * ((186583771 / 500000000000000000)) * (126 / 100) + 8 * ((186583771 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12622) *
          (32 * (((4653836041 / 1000000000000000000) : ℝ) + (310519671 / 200000000000000000) + (186583771 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12622 : ℝ) ^ 16 *
      (d.w0 12622 162 + d.w1 12622 162 * √(π / 2) + 2 * d.w2 12622 162 +
        energyR16 12622 * radiusPolynomialRoot16 (d.w0 12622 162) (d.w1 12622 162)
          (d.w2 12622 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12622 : ℝ) ^ 16 *
        (((29178089 / 1562500000000000000) : ℝ) + ((83038607 / 6250000000000000000)) * (126 / 100) + 2 * ((48544359 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12622) *
          (32 * (((29178089 / 1562500000000000000) : ℝ) + (83038607 / 6250000000000000000) + (48544359 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12622

/-! A coarse bound on the actual paper statistics constant at dimension 12623. -/
namespace BstLean.Part266.Row12623
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12621 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12621 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12621 128 ≤ (12875 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12875 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12623) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12623 : ℕ))
    (by norm_num : (12623 : ℕ) ≤ 16384)
  have ht : paperTail256 12623 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12623 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12623 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12623 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12623 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12623 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12621 128 * √(2 / (12623 : ℝ)) *
      (√(12623 : ℝ) + paperT0 12623 + paperTail256 12623) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12623 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12623 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12623 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12621 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12621 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12623 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12623

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12623
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12623 (61 / 100) 162 (17 / (100 * 12623)) (26 / (10 * 12623)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12623 (61 / 100) 162 (17 / (100 * 12623)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (97064603 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (192237591 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1343154863 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12623 / 12623 * (61 / 100)) ^ 4 * inverseRadius8 (12623 - 1) /
            envelopeGap 12623 (61 / 100) 162 (17 / (100 * 12623)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12623

namespace BstLean.Part266.Row12623
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12623 162 ≤ (2326456493 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12623 162 ≤ (1552290547 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (373093597 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12623 162 ≤ (93347681 / 5000000000000000000)
  w1 : (tableEnvelope C).w1 12623 162 ≤ (53132073 / 4000000000000000000)
  w2 : (tableEnvelope C).w2 12623 162 ≤ (24266411 / 5000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (97064603 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (97064603 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (192237591 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1343154863 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1834903 / 500000000) : ℝ) ≤ √(17 / (100 * 12623) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12623) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2203004801 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19608038709 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12623) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12623) ≤ (14004333 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12623) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12623 * (162 : ℝ) ^ 2 + 26 / (10 * 12623) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12623) : ℝ)) (tA 12623 * 162 ^ 2 + 26 / (10 * 12623)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1834903 / 500000000))) * ((97064603 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1834903 / 500000000)) ^ 3) * ((192237591 / 125000000000000000000000))) + ((1343154863 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1834903 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12623) : ℝ)) d.D d.V d.P (√(tA 12623) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1834903 / 500000000)) ^ 2 * (((2203004801 / 1000000000000000)) * ((19608038709 / 500000000000000000)))) + ((1343154863 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12623) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1834903 / 500000000)) * ((97064603 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12623) : ℝ)) (tA 12623 * 162 ^ 2 + 26 / (10 * 12623)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((97064603 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1834903 / 500000000)) ^ 2) * ((192237591 / 125000000000000000000000)) + ((1343154863 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12623) : ℝ)) (√(26 / (10 * 12623) : ℝ)) d.D d.V d.P (√(tA 12623) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1834903 / 500000000)) * (((2203004801 / 1000000000000000)) * ((19608038709 / 500000000000000000))) + ((1343154863 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12623) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((97064603 / 20000000000000000000) : ℝ) + ((1343154863 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12623

namespace BstLean.Part266.Row12623
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12623 162 ∧
    0 ≤ (tableEnvelope C).f1 12623 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12623 162 ∧
    0 ≤ (tableEnvelope C).w1 12623 162 ∧ 0 ≤ (tableEnvelope C).w2 12623 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12623 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12623 162 ∧ 0 ≤ d.f1 12623 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12623 162 ∧ 0 ≤ d.w1 12623 162 ∧ 0 ≤ d.w2 12623 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12623 ≤ 2 * (228 / 100 : ℝ) / 12623 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12623 ≤ 2 * (370 / 100 : ℝ) / 12623 := by
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
    (completeRAData (tableEnvelope C) 12623 162).locationBound 12623 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12623 162).energyBound 12623 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12623 162) (d.f1 12623 162) d.f2 ≤
      32 * (((2326456493 / 500000000000000000) : ℝ) + (1552290547 / 1000000000000000000) + (373093597 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12623 162) (d.w1 12623 162)
      (d.w2 12623 162) ≤
      32 * (((93347681 / 5000000000000000000) : ℝ) + (53132073 / 4000000000000000000) + (24266411 / 5000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12623 162) (d.f1 12623 162) d.f2 ≤
      ((2326456493 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2326456493 / 500000000000000000)) * ((1552290547 / 1000000000000000000)) * (126 / 100) +
      2 * (((1552290547 / 1000000000000000000)) ^ 2 + 2 * ((2326456493 / 500000000000000000)) * ((373093597 / 1000000000000000000))) +
      6 * ((1552290547 / 1000000000000000000)) * ((373093597 / 1000000000000000000)) * (126 / 100) + 8 * ((373093597 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12623 162) (d.f1 12623 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12623 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12623 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12623 162) (d.f1 12623 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12623 162) (d.w1 12623 162) (d.w2 12623 162)
  have hwexpr0 : 0 ≤ d.w0 12623 162 + d.w1 12623 162 * √(π / 2) +
      2 * d.w2 12623 162 + energyR16 12623 *
      radiusPolynomialRoot16 (d.w0 12623 162) (d.w1 12623 162) (d.w2 12623 162) := by
    positivity
  constructor
  · change (12623 : ℝ) ^ 8 * (mA 12623 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12623 162) (d.f1 12623 162) d.f2 + locationR16 12623 *
        radiusPolynomialRoot16 (d.f0 12623 162) (d.f1 12623 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12623 : ℝ) ^ 8 * (mA 12623 : ℝ) ^ 8 *
        ((((2326456493 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2326456493 / 500000000000000000)) * ((1552290547 / 1000000000000000000)) * (126 / 100) +
          2 * (((1552290547 / 1000000000000000000)) ^ 2 + 2 * ((2326456493 / 500000000000000000)) * ((373093597 / 1000000000000000000))) +
          6 * ((1552290547 / 1000000000000000000)) * ((373093597 / 1000000000000000000)) * (126 / 100) + 8 * ((373093597 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12623) *
          (32 * (((2326456493 / 500000000000000000) : ℝ) + (1552290547 / 1000000000000000000) + (373093597 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12623 : ℝ) ^ 16 *
      (d.w0 12623 162 + d.w1 12623 162 * √(π / 2) + 2 * d.w2 12623 162 +
        energyR16 12623 * radiusPolynomialRoot16 (d.w0 12623 162) (d.w1 12623 162)
          (d.w2 12623 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12623 : ℝ) ^ 16 *
        (((93347681 / 5000000000000000000) : ℝ) + ((53132073 / 4000000000000000000)) * (126 / 100) + 2 * ((24266411 / 5000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12623) *
          (32 * (((93347681 / 5000000000000000000) : ℝ) + (53132073 / 4000000000000000000) + (24266411 / 5000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12623

/-! A coarse bound on the actual paper statistics constant at dimension 12624. -/
namespace BstLean.Part266.Row12624
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12622 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12622 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12622 128 ≤ (12876 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12876 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12624) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12624 : ℕ))
    (by norm_num : (12624 : ℕ) ≤ 16384)
  have ht : paperTail256 12624 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12624 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12624 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12624 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12624 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12624 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12622 128 * √(2 / (12624 : ℝ)) *
      (√(12624 : ℝ) + paperT0 12624 + paperTail256 12624) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12624 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12624 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12624 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12622 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12622 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12624 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12624

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12624
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12624 (61 / 100) 162 (17 / (100 * 12624)) (26 / (10 * 12624)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12624 (61 / 100) 162 (17 / (100 * 12624)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (97041537 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (48044171 / 31250000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (671147819 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12624 / 12624 * (61 / 100)) ^ 4 * inverseRadius8 (12624 - 1) /
            envelopeGap 12624 (61 / 100) 162 (17 / (100 * 12624)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12624

namespace BstLean.Part266.Row12624
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12624 162 ≤ (4651990247 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12624 162 ≤ (775991419 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (93254919 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12624 162 ≤ (933254849 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12624 162 ≤ (331996511 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12624 162 ≤ (485212887 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (97041537 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (97041537 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (48044171 / 31250000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (671147819 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3669661 / 1000000000) : ℝ) ≤ √(17 / (100 * 12624) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12624) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2202743029 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19604932237 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12624) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12624) ≤ (11202579 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12624) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12624 * (162 : ℝ) ^ 2 + 26 / (10 * 12624) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12624) : ℝ)) (tA 12624 * 162 ^ 2 + 26 / (10 * 12624)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3669661 / 1000000000))) * ((97041537 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3669661 / 1000000000)) ^ 3) * ((48044171 / 31250000000000000000000))) + ((671147819 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3669661 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12624) : ℝ)) d.D d.V d.P (√(tA 12624) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3669661 / 1000000000)) ^ 2 * (((2202743029 / 1000000000000000)) * ((19604932237 / 500000000000000000)))) + ((671147819 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12624) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3669661 / 1000000000)) * ((97041537 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12624) : ℝ)) (tA 12624 * 162 ^ 2 + 26 / (10 * 12624)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((97041537 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3669661 / 1000000000)) ^ 2) * ((48044171 / 31250000000000000000000)) + ((671147819 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12624) : ℝ)) (√(26 / (10 * 12624) : ℝ)) d.D d.V d.P (√(tA 12624) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3669661 / 1000000000)) * (((2202743029 / 1000000000000000)) * ((19604932237 / 500000000000000000))) + ((671147819 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12624) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((97041537 / 20000000000000000000) : ℝ) + ((671147819 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12624

namespace BstLean.Part266.Row12624
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12624 162 ∧
    0 ≤ (tableEnvelope C).f1 12624 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12624 162 ∧
    0 ≤ (tableEnvelope C).w1 12624 162 ∧ 0 ≤ (tableEnvelope C).w2 12624 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12624 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12624 162 ∧ 0 ≤ d.f1 12624 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12624 162 ∧ 0 ≤ d.w1 12624 162 ∧ 0 ≤ d.w2 12624 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12624 ≤ 2 * (228 / 100 : ℝ) / 12624 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12624 ≤ 2 * (370 / 100 : ℝ) / 12624 := by
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
    (completeRAData (tableEnvelope C) 12624 162).locationBound 12624 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12624 162).energyBound 12624 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12624 162) (d.f1 12624 162) d.f2 ≤
      32 * (((4651990247 / 1000000000000000000) : ℝ) + (775991419 / 500000000000000000) + (93254919 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12624 162) (d.w1 12624 162)
      (d.w2 12624 162) ≤
      32 * (((933254849 / 50000000000000000000) : ℝ) + (331996511 / 25000000000000000000) + (485212887 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12624 162) (d.f1 12624 162) d.f2 ≤
      ((4651990247 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4651990247 / 1000000000000000000)) * ((775991419 / 500000000000000000)) * (126 / 100) +
      2 * (((775991419 / 500000000000000000)) ^ 2 + 2 * ((4651990247 / 1000000000000000000)) * ((93254919 / 250000000000000000))) +
      6 * ((775991419 / 500000000000000000)) * ((93254919 / 250000000000000000)) * (126 / 100) + 8 * ((93254919 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12624 162) (d.f1 12624 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12624 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12624 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12624 162) (d.f1 12624 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12624 162) (d.w1 12624 162) (d.w2 12624 162)
  have hwexpr0 : 0 ≤ d.w0 12624 162 + d.w1 12624 162 * √(π / 2) +
      2 * d.w2 12624 162 + energyR16 12624 *
      radiusPolynomialRoot16 (d.w0 12624 162) (d.w1 12624 162) (d.w2 12624 162) := by
    positivity
  constructor
  · change (12624 : ℝ) ^ 8 * (mA 12624 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12624 162) (d.f1 12624 162) d.f2 + locationR16 12624 *
        radiusPolynomialRoot16 (d.f0 12624 162) (d.f1 12624 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12624 : ℝ) ^ 8 * (mA 12624 : ℝ) ^ 8 *
        ((((4651990247 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4651990247 / 1000000000000000000)) * ((775991419 / 500000000000000000)) * (126 / 100) +
          2 * (((775991419 / 500000000000000000)) ^ 2 + 2 * ((4651990247 / 1000000000000000000)) * ((93254919 / 250000000000000000))) +
          6 * ((775991419 / 500000000000000000)) * ((93254919 / 250000000000000000)) * (126 / 100) + 8 * ((93254919 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12624) *
          (32 * (((4651990247 / 1000000000000000000) : ℝ) + (775991419 / 500000000000000000) + (93254919 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12624 : ℝ) ^ 16 *
      (d.w0 12624 162 + d.w1 12624 162 * √(π / 2) + 2 * d.w2 12624 162 +
        energyR16 12624 * radiusPolynomialRoot16 (d.w0 12624 162) (d.w1 12624 162)
          (d.w2 12624 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12624 : ℝ) ^ 16 *
        (((933254849 / 50000000000000000000) : ℝ) + ((331996511 / 25000000000000000000)) * (126 / 100) + 2 * ((485212887 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12624) *
          (32 * (((933254849 / 50000000000000000000) : ℝ) + (331996511 / 25000000000000000000) + (485212887 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12624
