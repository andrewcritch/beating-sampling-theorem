import BstLean.Part266Shard11Step4


/-! A coarse bound on the actual paper statistics constant at dimension 12625. -/
namespace BstLean.Part266.Row12625
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12623 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12623 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12623 128 ≤ (12877 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12877 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12625) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12625 : ℕ))
    (by norm_num : (12625 : ℕ) ≤ 16384)
  have ht : paperTail256 12625 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12625 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12625 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12625 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12625 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12625 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12623 128 * √(2 / (12625 : ℝ)) *
      (√(12625 : ℝ) + paperT0 12625 + paperTail256 12625) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12625 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12625 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12625 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12623 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12623 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12625 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12625

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12625
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12625 (61 / 100) 162 (17 / (100 * 12625)) (26 / (10 * 12625)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12625 (61 / 100) 162 (17 / (100 * 12625)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (485092391 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1536926409 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5365748127 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12625 / 12625 * (61 / 100)) ^ 4 * inverseRadius8 (12625 - 1) /
            envelopeGap 12625 (61 / 100) 162 (17 / (100 * 12625)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12625

namespace BstLean.Part266.Row12625
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12625 162 ≤ (930214297 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12625 162 ≤ (62067043 / 40000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (372945877 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12625 162 ≤ (1866066681 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12625 162 ≤ (1327670731 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12625 162 ≤ (485097589 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (485092391 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (485092391 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1536926409 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5365748127 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((733903 / 200000000) : ℝ) ≤ √(17 / (100 * 12625) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12625) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (550620327 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19601826503 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12625) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12625) ≤ (28004229 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12625) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12625 * (162 : ℝ) ^ 2 + 26 / (10 * 12625) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12625) : ℝ)) (tA 12625 * 162 ^ 2 + 26 / (10 * 12625)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((733903 / 200000000))) * ((485092391 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((733903 / 200000000)) ^ 3) * ((1536926409 / 1000000000000000000000000))) + ((5365748127 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((733903 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12625) : ℝ)) d.D d.V d.P (√(tA 12625) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((733903 / 200000000)) ^ 2 * (((550620327 / 250000000000000)) * ((19601826503 / 500000000000000000)))) + ((5365748127 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12625) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((733903 / 200000000)) * ((485092391 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12625) : ℝ)) (tA 12625 * 162 ^ 2 + 26 / (10 * 12625)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((485092391 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((733903 / 200000000)) ^ 2) * ((1536926409 / 1000000000000000000000000)) + ((5365748127 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12625) : ℝ)) (√(26 / (10 * 12625) : ℝ)) d.D d.V d.P (√(tA 12625) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((733903 / 200000000)) * (((550620327 / 250000000000000)) * ((19601826503 / 500000000000000000))) + ((5365748127 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12625) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((485092391 / 100000000000000000000) : ℝ) + ((5365748127 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12625

namespace BstLean.Part266.Row12625
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12625 162 ∧
    0 ≤ (tableEnvelope C).f1 12625 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12625 162 ∧
    0 ≤ (tableEnvelope C).w1 12625 162 ∧ 0 ≤ (tableEnvelope C).w2 12625 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12625 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12625 162 ∧ 0 ≤ d.f1 12625 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12625 162 ∧ 0 ≤ d.w1 12625 162 ∧ 0 ≤ d.w2 12625 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12625 ≤ 2 * (228 / 100 : ℝ) / 12625 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12625 ≤ 2 * (370 / 100 : ℝ) / 12625 := by
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
    (completeRAData (tableEnvelope C) 12625 162).locationBound 12625 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12625 162).energyBound 12625 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12625 162) (d.f1 12625 162) d.f2 ≤
      32 * (((930214297 / 200000000000000000) : ℝ) + (62067043 / 40000000000000000) + (372945877 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12625 162) (d.w1 12625 162)
      (d.w2 12625 162) ≤
      32 * (((1866066681 / 100000000000000000000) : ℝ) + (1327670731 / 100000000000000000000) + (485097589 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12625 162) (d.f1 12625 162) d.f2 ≤
      ((930214297 / 200000000000000000) : ℝ) ^ 2 + 2 * ((930214297 / 200000000000000000)) * ((62067043 / 40000000000000000)) * (126 / 100) +
      2 * (((62067043 / 40000000000000000)) ^ 2 + 2 * ((930214297 / 200000000000000000)) * ((372945877 / 1000000000000000000))) +
      6 * ((62067043 / 40000000000000000)) * ((372945877 / 1000000000000000000)) * (126 / 100) + 8 * ((372945877 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12625 162) (d.f1 12625 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12625 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12625 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12625 162) (d.f1 12625 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12625 162) (d.w1 12625 162) (d.w2 12625 162)
  have hwexpr0 : 0 ≤ d.w0 12625 162 + d.w1 12625 162 * √(π / 2) +
      2 * d.w2 12625 162 + energyR16 12625 *
      radiusPolynomialRoot16 (d.w0 12625 162) (d.w1 12625 162) (d.w2 12625 162) := by
    positivity
  constructor
  · change (12625 : ℝ) ^ 8 * (mA 12625 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12625 162) (d.f1 12625 162) d.f2 + locationR16 12625 *
        radiusPolynomialRoot16 (d.f0 12625 162) (d.f1 12625 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12625 : ℝ) ^ 8 * (mA 12625 : ℝ) ^ 8 *
        ((((930214297 / 200000000000000000) : ℝ) ^ 2 + 2 * ((930214297 / 200000000000000000)) * ((62067043 / 40000000000000000)) * (126 / 100) +
          2 * (((62067043 / 40000000000000000)) ^ 2 + 2 * ((930214297 / 200000000000000000)) * ((372945877 / 1000000000000000000))) +
          6 * ((62067043 / 40000000000000000)) * ((372945877 / 1000000000000000000)) * (126 / 100) + 8 * ((372945877 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12625) *
          (32 * (((930214297 / 200000000000000000) : ℝ) + (62067043 / 40000000000000000) + (372945877 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12625 : ℝ) ^ 16 *
      (d.w0 12625 162 + d.w1 12625 162 * √(π / 2) + 2 * d.w2 12625 162 +
        energyR16 12625 * radiusPolynomialRoot16 (d.w0 12625 162) (d.w1 12625 162)
          (d.w2 12625 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12625 : ℝ) ^ 16 *
        (((1866066681 / 100000000000000000000) : ℝ) + ((1327670731 / 100000000000000000000)) * (126 / 100) + 2 * ((485097589 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12625) *
          (32 * (((1866066681 / 100000000000000000000) : ℝ) + (1327670731 / 100000000000000000000) + (485097589 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12625

/-! A coarse bound on the actual paper statistics constant at dimension 12626. -/
namespace BstLean.Part266.Row12626
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12624 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12624 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12624 128 ≤ (12878 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12878 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12626) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12626 : ℕ))
    (by norm_num : (12626 : ℕ) ≤ 16384)
  have ht : paperTail256 12626 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12626 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12626 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12626 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12626 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12626 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12624 128 * √(2 / (12626 : ℝ)) *
      (√(12626 : ℝ) + paperT0 12626 + paperTail256 12626) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12626 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12626 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12626 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12624 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12624 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12626 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12626

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12626
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12626 (61 / 100) 162 (17 / (100 * 12626)) (26 / (10 * 12626)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12626 (61 / 100) 162 (17 / (100 * 12626)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (242488567 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1536439539 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (335144761 / 62500000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12626 / 12626 * (61 / 100)) ^ 4 * inverseRadius8 (12626 - 1) /
            envelopeGap 12626 (61 / 100) 162 (17 / (100 * 12626)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12626

namespace BstLean.Part266.Row12626
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12626 162 ≤ (581268673 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12626 162 ≤ (775684283 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (46609 / 125000000000000)
  w0 : (tableEnvelope C).w0 12626 162 ≤ (932811533 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12626 162 ≤ (1327355163 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12626 162 ≤ (484982329 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (242488567 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (242488567 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1536439539 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (335144761 / 62500000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((366937 / 100000000) : ℝ) ≤ √(17 / (100 * 12626) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12626) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (55055491 / 25000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39197443017 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12626) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12626) ≤ (28002011 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12626) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12626 * (162 : ℝ) ^ 2 + 26 / (10 * 12626) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12626) : ℝ)) (tA 12626 * 162 ^ 2 + 26 / (10 * 12626)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((366937 / 100000000))) * ((242488567 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((366937 / 100000000)) ^ 3) * ((1536439539 / 1000000000000000000000000))) + ((335144761 / 62500000000000000000000)) * (3 / 2 * (39895 / 100000) / ((366937 / 100000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12626) : ℝ)) d.D d.V d.P (√(tA 12626) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((366937 / 100000000)) ^ 2 * (((55055491 / 25000000000000)) * ((39197443017 / 1000000000000000000)))) + ((335144761 / 62500000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12626) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((366937 / 100000000)) * ((242488567 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12626) : ℝ)) (tA 12626 * 162 ^ 2 + 26 / (10 * 12626)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((242488567 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((366937 / 100000000)) ^ 2) * ((1536439539 / 1000000000000000000000000)) + ((335144761 / 62500000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12626) : ℝ)) (√(26 / (10 * 12626) : ℝ)) d.D d.V d.P (√(tA 12626) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((366937 / 100000000)) * (((55055491 / 25000000000000)) * ((39197443017 / 1000000000000000000))) + ((335144761 / 62500000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12626) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((242488567 / 50000000000000000000) : ℝ) + ((335144761 / 62500000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12626

namespace BstLean.Part266.Row12626
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12626 162 ∧
    0 ≤ (tableEnvelope C).f1 12626 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12626 162 ∧
    0 ≤ (tableEnvelope C).w1 12626 162 ∧ 0 ≤ (tableEnvelope C).w2 12626 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12626 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12626 162 ∧ 0 ≤ d.f1 12626 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12626 162 ∧ 0 ≤ d.w1 12626 162 ∧ 0 ≤ d.w2 12626 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12626 ≤ 2 * (228 / 100 : ℝ) / 12626 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12626 ≤ 2 * (370 / 100 : ℝ) / 12626 := by
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
    (completeRAData (tableEnvelope C) 12626 162).locationBound 12626 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12626 162).energyBound 12626 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12626 162) (d.f1 12626 162) d.f2 ≤
      32 * (((581268673 / 125000000000000000) : ℝ) + (775684283 / 500000000000000000) + (46609 / 125000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12626 162) (d.w1 12626 162)
      (d.w2 12626 162) ≤
      32 * (((932811533 / 50000000000000000000) : ℝ) + (1327355163 / 100000000000000000000) + (484982329 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12626 162) (d.f1 12626 162) d.f2 ≤
      ((581268673 / 125000000000000000) : ℝ) ^ 2 + 2 * ((581268673 / 125000000000000000)) * ((775684283 / 500000000000000000)) * (126 / 100) +
      2 * (((775684283 / 500000000000000000)) ^ 2 + 2 * ((581268673 / 125000000000000000)) * ((46609 / 125000000000000))) +
      6 * ((775684283 / 500000000000000000)) * ((46609 / 125000000000000)) * (126 / 100) + 8 * ((46609 / 125000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12626 162) (d.f1 12626 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12626 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12626 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12626 162) (d.f1 12626 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12626 162) (d.w1 12626 162) (d.w2 12626 162)
  have hwexpr0 : 0 ≤ d.w0 12626 162 + d.w1 12626 162 * √(π / 2) +
      2 * d.w2 12626 162 + energyR16 12626 *
      radiusPolynomialRoot16 (d.w0 12626 162) (d.w1 12626 162) (d.w2 12626 162) := by
    positivity
  constructor
  · change (12626 : ℝ) ^ 8 * (mA 12626 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12626 162) (d.f1 12626 162) d.f2 + locationR16 12626 *
        radiusPolynomialRoot16 (d.f0 12626 162) (d.f1 12626 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12626 : ℝ) ^ 8 * (mA 12626 : ℝ) ^ 8 *
        ((((581268673 / 125000000000000000) : ℝ) ^ 2 + 2 * ((581268673 / 125000000000000000)) * ((775684283 / 500000000000000000)) * (126 / 100) +
          2 * (((775684283 / 500000000000000000)) ^ 2 + 2 * ((581268673 / 125000000000000000)) * ((46609 / 125000000000000))) +
          6 * ((775684283 / 500000000000000000)) * ((46609 / 125000000000000)) * (126 / 100) + 8 * ((46609 / 125000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12626) *
          (32 * (((581268673 / 125000000000000000) : ℝ) + (775684283 / 500000000000000000) + (46609 / 125000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12626 : ℝ) ^ 16 *
      (d.w0 12626 162 + d.w1 12626 162 * √(π / 2) + 2 * d.w2 12626 162 +
        energyR16 12626 * radiusPolynomialRoot16 (d.w0 12626 162) (d.w1 12626 162)
          (d.w2 12626 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12626 : ℝ) ^ 16 *
        (((932811533 / 50000000000000000000) : ℝ) + ((1327355163 / 100000000000000000000)) * (126 / 100) + 2 * ((484982329 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12626) *
          (32 * (((932811533 / 50000000000000000000) : ℝ) + (1327355163 / 100000000000000000000) + (484982329 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12626

/-! A coarse bound on the actual paper statistics constant at dimension 12627. -/
namespace BstLean.Part266.Row12627
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12625 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12625 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12625 128 ≤ (12879 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12879 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12627) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12627 : ℕ))
    (by norm_num : (12627 : ℕ) ≤ 16384)
  have ht : paperTail256 12627 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12627 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12627 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12627 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12627 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12627 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12625 128 * √(2 / (12627 : ℝ)) *
      (√(12627 : ℝ) + paperT0 12627 + paperTail256 12627) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12627 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12627 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12627 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12625 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12625 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12627 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12627

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12627
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12627 (61 / 100) 162 (17 / (100 * 12627)) (26 / (10 * 12627)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12627 (61 / 100) 162 (17 / (100 * 12627)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (484861913 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (767976431 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5358886697 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12627 / 12627 * (61 / 100)) ^ 4 * inverseRadius8 (12627 - 1) /
            envelopeGap 12627 (61 / 100) 162 (17 / (100 * 12627)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12627

namespace BstLean.Part266.Row12627
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12627 162 ≤ (2324613801 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12627 162 ≤ (387765289 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (74559629 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12627 162 ≤ (466294901 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12627 162 ≤ (13270397 / 1000000000000000000)
  w2 : (tableEnvelope C).w2 12627 162 ≤ (96973421 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (484861913 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (484861913 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (767976431 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5358886697 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((146769 / 40000000) : ℝ) ≤ √(17 / (100 * 12627) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12627) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1100979011 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7838246901 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12627) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12627) ≤ (55999587 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12627) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12627 * (162 : ℝ) ^ 2 + 26 / (10 * 12627) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12627) : ℝ)) (tA 12627 * 162 ^ 2 + 26 / (10 * 12627)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((146769 / 40000000))) * ((484861913 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((146769 / 40000000)) ^ 3) * ((767976431 / 500000000000000000000000))) + ((5358886697 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((146769 / 40000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12627) : ℝ)) d.D d.V d.P (√(tA 12627) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((146769 / 40000000)) ^ 2 * (((1100979011 / 500000000000000)) * ((7838246901 / 200000000000000000)))) + ((5358886697 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12627) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((146769 / 40000000)) * ((484861913 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12627) : ℝ)) (tA 12627 * 162 ^ 2 + 26 / (10 * 12627)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((484861913 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((146769 / 40000000)) ^ 2) * ((767976431 / 500000000000000000000000)) + ((5358886697 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12627) : ℝ)) (√(26 / (10 * 12627) : ℝ)) d.D d.V d.P (√(tA 12627) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((146769 / 40000000)) * (((1100979011 / 500000000000000)) * ((7838246901 / 200000000000000000))) + ((5358886697 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12627) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((484861913 / 100000000000000000000) : ℝ) + ((5358886697 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12627

namespace BstLean.Part266.Row12627
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12627 162 ∧
    0 ≤ (tableEnvelope C).f1 12627 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12627 162 ∧
    0 ≤ (tableEnvelope C).w1 12627 162 ∧ 0 ≤ (tableEnvelope C).w2 12627 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12627 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12627 162 ∧ 0 ≤ d.f1 12627 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12627 162 ∧ 0 ≤ d.w1 12627 162 ∧ 0 ≤ d.w2 12627 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12627 ≤ 2 * (228 / 100 : ℝ) / 12627 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12627 ≤ 2 * (370 / 100 : ℝ) / 12627 := by
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
    (completeRAData (tableEnvelope C) 12627 162).locationBound 12627 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12627 162).energyBound 12627 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12627 162) (d.f1 12627 162) d.f2 ≤
      32 * (((2324613801 / 500000000000000000) : ℝ) + (387765289 / 250000000000000000) + (74559629 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12627 162) (d.w1 12627 162)
      (d.w2 12627 162) ≤
      32 * (((466294901 / 25000000000000000000) : ℝ) + (13270397 / 1000000000000000000) + (96973421 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12627 162) (d.f1 12627 162) d.f2 ≤
      ((2324613801 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2324613801 / 500000000000000000)) * ((387765289 / 250000000000000000)) * (126 / 100) +
      2 * (((387765289 / 250000000000000000)) ^ 2 + 2 * ((2324613801 / 500000000000000000)) * ((74559629 / 200000000000000000))) +
      6 * ((387765289 / 250000000000000000)) * ((74559629 / 200000000000000000)) * (126 / 100) + 8 * ((74559629 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12627 162) (d.f1 12627 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12627 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12627 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12627 162) (d.f1 12627 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12627 162) (d.w1 12627 162) (d.w2 12627 162)
  have hwexpr0 : 0 ≤ d.w0 12627 162 + d.w1 12627 162 * √(π / 2) +
      2 * d.w2 12627 162 + energyR16 12627 *
      radiusPolynomialRoot16 (d.w0 12627 162) (d.w1 12627 162) (d.w2 12627 162) := by
    positivity
  constructor
  · change (12627 : ℝ) ^ 8 * (mA 12627 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12627 162) (d.f1 12627 162) d.f2 + locationR16 12627 *
        radiusPolynomialRoot16 (d.f0 12627 162) (d.f1 12627 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12627 : ℝ) ^ 8 * (mA 12627 : ℝ) ^ 8 *
        ((((2324613801 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2324613801 / 500000000000000000)) * ((387765289 / 250000000000000000)) * (126 / 100) +
          2 * (((387765289 / 250000000000000000)) ^ 2 + 2 * ((2324613801 / 500000000000000000)) * ((74559629 / 200000000000000000))) +
          6 * ((387765289 / 250000000000000000)) * ((74559629 / 200000000000000000)) * (126 / 100) + 8 * ((74559629 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12627) *
          (32 * (((2324613801 / 500000000000000000) : ℝ) + (387765289 / 250000000000000000) + (74559629 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12627 : ℝ) ^ 16 *
      (d.w0 12627 162 + d.w1 12627 162 * √(π / 2) + 2 * d.w2 12627 162 +
        energyR16 12627 * radiusPolynomialRoot16 (d.w0 12627 162) (d.w1 12627 162)
          (d.w2 12627 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12627 : ℝ) ^ 16 *
        (((466294901 / 25000000000000000000) : ℝ) + ((13270397 / 1000000000000000000)) * (126 / 100) + 2 * ((96973421 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12627) *
          (32 * (((466294901 / 25000000000000000000) : ℝ) + (13270397 / 1000000000000000000) + (96973421 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12627

/-! A coarse bound on the actual paper statistics constant at dimension 12628. -/
namespace BstLean.Part266.Row12628
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12626 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12626 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12626 128 ≤ (12880 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12880 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12628) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12628 : ℕ))
    (by norm_num : (12628 : ℕ) ≤ 16384)
  have ht : paperTail256 12628 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12628 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12628 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12628 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12628 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12628 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12626 128 * √(2 / (12628 : ℝ)) *
      (√(12628 : ℝ) + paperT0 12628 + paperTail256 12628) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12628 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12628 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12628 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12626 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12626 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12628 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12628

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12628
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12628 (61 / 100) 162 (17 / (100 * 12628)) (26 / (10 * 12628)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12628 (61 / 100) 162 (17 / (100 * 12628)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (60593341 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (767733189 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5355459687 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12628 / 12628 * (61 / 100)) ^ 4 * inverseRadius8 (12628 - 1) /
            envelopeGap 12628 (61 / 100) 162 (17 / (100 * 12628)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12628

namespace BstLean.Part266.Row12628
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12628 162 ≤ (1162077449 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12628 162 ≤ (387688673 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (372724413 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12628 162 ≤ (233092131 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 12628 162 ≤ (663362353 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12628 162 ≤ (121187979 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (60593341 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (60593341 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (767733189 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5355459687 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3669079 / 1000000000) : ℝ) ≤ √(17 / (100 * 12628) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12628) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (275212057 / 125000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39185027473 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12628) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12628) ≤ (22398061 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12628) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12628 * (162 : ℝ) ^ 2 + 26 / (10 * 12628) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12628) : ℝ)) (tA 12628 * 162 ^ 2 + 26 / (10 * 12628)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3669079 / 1000000000))) * ((60593341 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3669079 / 1000000000)) ^ 3) * ((767733189 / 500000000000000000000000))) + ((5355459687 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3669079 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12628) : ℝ)) d.D d.V d.P (√(tA 12628) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3669079 / 1000000000)) ^ 2 * (((275212057 / 125000000000000)) * ((39185027473 / 1000000000000000000)))) + ((5355459687 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12628) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3669079 / 1000000000)) * ((60593341 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12628) : ℝ)) (tA 12628 * 162 ^ 2 + 26 / (10 * 12628)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((60593341 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3669079 / 1000000000)) ^ 2) * ((767733189 / 500000000000000000000000)) + ((5355459687 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12628) : ℝ)) (√(26 / (10 * 12628) : ℝ)) d.D d.V d.P (√(tA 12628) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3669079 / 1000000000)) * (((275212057 / 125000000000000)) * ((39185027473 / 1000000000000000000))) + ((5355459687 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12628) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((60593341 / 12500000000000000000) : ℝ) + ((5355459687 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12628

namespace BstLean.Part266.Row12628
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12628 162 ∧
    0 ≤ (tableEnvelope C).f1 12628 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12628 162 ∧
    0 ≤ (tableEnvelope C).w1 12628 162 ∧ 0 ≤ (tableEnvelope C).w2 12628 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12628 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12628 162 ∧ 0 ≤ d.f1 12628 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12628 162 ∧ 0 ≤ d.w1 12628 162 ∧ 0 ≤ d.w2 12628 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12628 ≤ 2 * (228 / 100 : ℝ) / 12628 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12628 ≤ 2 * (370 / 100 : ℝ) / 12628 := by
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
    (completeRAData (tableEnvelope C) 12628 162).locationBound 12628 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12628 162).energyBound 12628 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12628 162) (d.f1 12628 162) d.f2 ≤
      32 * (((1162077449 / 250000000000000000) : ℝ) + (387688673 / 250000000000000000) + (372724413 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12628 162) (d.w1 12628 162)
      (d.w2 12628 162) ≤
      32 * (((233092131 / 12500000000000000000) : ℝ) + (663362353 / 50000000000000000000) + (121187979 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12628 162) (d.f1 12628 162) d.f2 ≤
      ((1162077449 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1162077449 / 250000000000000000)) * ((387688673 / 250000000000000000)) * (126 / 100) +
      2 * (((387688673 / 250000000000000000)) ^ 2 + 2 * ((1162077449 / 250000000000000000)) * ((372724413 / 1000000000000000000))) +
      6 * ((387688673 / 250000000000000000)) * ((372724413 / 1000000000000000000)) * (126 / 100) + 8 * ((372724413 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12628 162) (d.f1 12628 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12628 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12628 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12628 162) (d.f1 12628 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12628 162) (d.w1 12628 162) (d.w2 12628 162)
  have hwexpr0 : 0 ≤ d.w0 12628 162 + d.w1 12628 162 * √(π / 2) +
      2 * d.w2 12628 162 + energyR16 12628 *
      radiusPolynomialRoot16 (d.w0 12628 162) (d.w1 12628 162) (d.w2 12628 162) := by
    positivity
  constructor
  · change (12628 : ℝ) ^ 8 * (mA 12628 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12628 162) (d.f1 12628 162) d.f2 + locationR16 12628 *
        radiusPolynomialRoot16 (d.f0 12628 162) (d.f1 12628 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12628 : ℝ) ^ 8 * (mA 12628 : ℝ) ^ 8 *
        ((((1162077449 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1162077449 / 250000000000000000)) * ((387688673 / 250000000000000000)) * (126 / 100) +
          2 * (((387688673 / 250000000000000000)) ^ 2 + 2 * ((1162077449 / 250000000000000000)) * ((372724413 / 1000000000000000000))) +
          6 * ((387688673 / 250000000000000000)) * ((372724413 / 1000000000000000000)) * (126 / 100) + 8 * ((372724413 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12628) *
          (32 * (((1162077449 / 250000000000000000) : ℝ) + (387688673 / 250000000000000000) + (372724413 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12628 : ℝ) ^ 16 *
      (d.w0 12628 162 + d.w1 12628 162 * √(π / 2) + 2 * d.w2 12628 162 +
        energyR16 12628 * radiusPolynomialRoot16 (d.w0 12628 162) (d.w1 12628 162)
          (d.w2 12628 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12628 : ℝ) ^ 16 *
        (((233092131 / 12500000000000000000) : ℝ) + ((663362353 / 50000000000000000000)) * (126 / 100) + 2 * ((121187979 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12628) *
          (32 * (((233092131 / 12500000000000000000) : ℝ) + (663362353 / 50000000000000000000) + (121187979 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12628

/-! A coarse bound on the actual paper statistics constant at dimension 12629. -/
namespace BstLean.Part266.Row12629
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12627 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12627 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12627 128 ≤ (12881 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12881 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12629) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12629 : ℕ))
    (by norm_num : (12629 : ℕ) ≤ 16384)
  have ht : paperTail256 12629 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12629 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12629 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12629 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12629 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12629 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12627 128 * √(2 / (12629 : ℝ)) *
      (√(12629 : ℝ) + paperT0 12629 + paperTail256 12629) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12629 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12629 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12629 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12627 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12627 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12629 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12629

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12629
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12629 (61 / 100) 162 (17 / (100 * 12629)) (26 / (10 * 12629)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12629 (61 / 100) 162 (17 / (100 * 12629)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (484631581 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (767490043 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2676017573 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12629 / 12629 * (61 / 100)) ^ 4 * inverseRadius8 (12629 - 1) /
            envelopeGap 12629 (61 / 100) 162 (17 / (100 * 12629)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12629

namespace BstLean.Part266.Row12629
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12629 162 ≤ (92947773 / 20000000000000000)
  f1 : (tableEnvelope C).f1 12629 162 ≤ (1550447483 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (372650603 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12629 162 ≤ (932146947 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12629 162 ≤ (82900591 / 6250000000000000000)
  w2 : (tableEnvelope C).w2 12629 162 ≤ (242318383 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (484631581 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (484631581 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (767490043 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2676017573 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1834467 / 500000000) : ℝ) ≤ √(17 / (100 * 12629) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12629) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (34397421 / 15625000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39178821907 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12629) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12629) ≤ (111981437 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12629) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12629 * (162 : ℝ) ^ 2 + 26 / (10 * 12629) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12629) : ℝ)) (tA 12629 * 162 ^ 2 + 26 / (10 * 12629)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1834467 / 500000000))) * ((484631581 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1834467 / 500000000)) ^ 3) * ((767490043 / 500000000000000000000000))) + ((2676017573 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1834467 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12629) : ℝ)) d.D d.V d.P (√(tA 12629) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1834467 / 500000000)) ^ 2 * (((34397421 / 15625000000000)) * ((39178821907 / 1000000000000000000)))) + ((2676017573 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12629) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1834467 / 500000000)) * ((484631581 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12629) : ℝ)) (tA 12629 * 162 ^ 2 + 26 / (10 * 12629)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((484631581 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1834467 / 500000000)) ^ 2) * ((767490043 / 500000000000000000000000)) + ((2676017573 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12629) : ℝ)) (√(26 / (10 * 12629) : ℝ)) d.D d.V d.P (√(tA 12629) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1834467 / 500000000)) * (((34397421 / 15625000000000)) * ((39178821907 / 1000000000000000000))) + ((2676017573 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12629) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((484631581 / 100000000000000000000) : ℝ) + ((2676017573 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12629

namespace BstLean.Part266.Row12629
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12629 162 ∧
    0 ≤ (tableEnvelope C).f1 12629 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12629 162 ∧
    0 ≤ (tableEnvelope C).w1 12629 162 ∧ 0 ≤ (tableEnvelope C).w2 12629 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12629 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12629 162 ∧ 0 ≤ d.f1 12629 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12629 162 ∧ 0 ≤ d.w1 12629 162 ∧ 0 ≤ d.w2 12629 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12629 ≤ 2 * (228 / 100 : ℝ) / 12629 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12629 ≤ 2 * (370 / 100 : ℝ) / 12629 := by
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
    (completeRAData (tableEnvelope C) 12629 162).locationBound 12629 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12629 162).energyBound 12629 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12629 162) (d.f1 12629 162) d.f2 ≤
      32 * (((92947773 / 20000000000000000) : ℝ) + (1550447483 / 1000000000000000000) + (372650603 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12629 162) (d.w1 12629 162)
      (d.w2 12629 162) ≤
      32 * (((932146947 / 50000000000000000000) : ℝ) + (82900591 / 6250000000000000000) + (242318383 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12629 162) (d.f1 12629 162) d.f2 ≤
      ((92947773 / 20000000000000000) : ℝ) ^ 2 + 2 * ((92947773 / 20000000000000000)) * ((1550447483 / 1000000000000000000)) * (126 / 100) +
      2 * (((1550447483 / 1000000000000000000)) ^ 2 + 2 * ((92947773 / 20000000000000000)) * ((372650603 / 1000000000000000000))) +
      6 * ((1550447483 / 1000000000000000000)) * ((372650603 / 1000000000000000000)) * (126 / 100) + 8 * ((372650603 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12629 162) (d.f1 12629 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12629 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12629 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12629 162) (d.f1 12629 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12629 162) (d.w1 12629 162) (d.w2 12629 162)
  have hwexpr0 : 0 ≤ d.w0 12629 162 + d.w1 12629 162 * √(π / 2) +
      2 * d.w2 12629 162 + energyR16 12629 *
      radiusPolynomialRoot16 (d.w0 12629 162) (d.w1 12629 162) (d.w2 12629 162) := by
    positivity
  constructor
  · change (12629 : ℝ) ^ 8 * (mA 12629 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12629 162) (d.f1 12629 162) d.f2 + locationR16 12629 *
        radiusPolynomialRoot16 (d.f0 12629 162) (d.f1 12629 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12629 : ℝ) ^ 8 * (mA 12629 : ℝ) ^ 8 *
        ((((92947773 / 20000000000000000) : ℝ) ^ 2 + 2 * ((92947773 / 20000000000000000)) * ((1550447483 / 1000000000000000000)) * (126 / 100) +
          2 * (((1550447483 / 1000000000000000000)) ^ 2 + 2 * ((92947773 / 20000000000000000)) * ((372650603 / 1000000000000000000))) +
          6 * ((1550447483 / 1000000000000000000)) * ((372650603 / 1000000000000000000)) * (126 / 100) + 8 * ((372650603 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12629) *
          (32 * (((92947773 / 20000000000000000) : ℝ) + (1550447483 / 1000000000000000000) + (372650603 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12629 : ℝ) ^ 16 *
      (d.w0 12629 162 + d.w1 12629 162 * √(π / 2) + 2 * d.w2 12629 162 +
        energyR16 12629 * radiusPolynomialRoot16 (d.w0 12629 162) (d.w1 12629 162)
          (d.w2 12629 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12629 : ℝ) ^ 16 *
        (((932146947 / 50000000000000000000) : ℝ) + ((82900591 / 6250000000000000000)) * (126 / 100) + 2 * ((242318383 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12629) *
          (32 * (((932146947 / 50000000000000000000) : ℝ) + (82900591 / 6250000000000000000) + (242318383 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12629

/-! A coarse bound on the actual paper statistics constant at dimension 12630. -/
namespace BstLean.Part266.Row12630
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12628 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12628 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12628 128 ≤ (12882 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12882 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12630) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12630 : ℕ))
    (by norm_num : (12630 : ℕ) ≤ 16384)
  have ht : paperTail256 12630 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12630 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12630 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12630 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12630 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12630 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12628 128 * √(2 / (12630 : ℝ)) *
      (√(12630 : ℝ) + paperT0 12630 + paperTail256 12630) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12630 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12630 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12630 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12628 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12628 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12630 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12630

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12630
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12630 (61 / 100) 162 (17 / (100 * 12630)) (26 / (10 * 12630)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12630 (61 / 100) 162 (17 / (100 * 12630)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (484516469 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1534493987 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (534861307 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12630 / 12630 * (61 / 100)) ^ 4 * inverseRadius8 (12630 - 1) /
            envelopeGap 12630 (61 / 100) 162 (17 / (100 * 12630)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12630

namespace BstLean.Part266.Row12630
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12630 162 ≤ (290404239 / 62500000000000000)
  f1 : (tableEnvelope C).f1 12630 162 ≤ (387535093 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (372576813 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12630 162 ≤ (465962723 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12630 162 ≤ (165761789 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 12630 162 ≤ (484521651 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (484516469 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (484516469 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1534493987 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (534861307 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3668789 / 1000000000) : ℝ) ≤ √(17 / (100 * 12630) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12630) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2201173481 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19586308911 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12630) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12630) ≤ (111972571 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12630) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12630 * (162 : ℝ) ^ 2 + 26 / (10 * 12630) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12630) : ℝ)) (tA 12630 * 162 ^ 2 + 26 / (10 * 12630)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3668789 / 1000000000))) * ((484516469 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3668789 / 1000000000)) ^ 3) * ((1534493987 / 1000000000000000000000000))) + ((534861307 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3668789 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12630) : ℝ)) d.D d.V d.P (√(tA 12630) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3668789 / 1000000000)) ^ 2 * (((2201173481 / 1000000000000000)) * ((19586308911 / 500000000000000000)))) + ((534861307 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12630) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3668789 / 1000000000)) * ((484516469 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12630) : ℝ)) (tA 12630 * 162 ^ 2 + 26 / (10 * 12630)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((484516469 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3668789 / 1000000000)) ^ 2) * ((1534493987 / 1000000000000000000000000)) + ((534861307 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12630) : ℝ)) (√(26 / (10 * 12630) : ℝ)) d.D d.V d.P (√(tA 12630) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3668789 / 1000000000)) * (((2201173481 / 1000000000000000)) * ((19586308911 / 500000000000000000))) + ((534861307 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12630) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((484516469 / 100000000000000000000) : ℝ) + ((534861307 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12630

namespace BstLean.Part266.Row12630
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12630 162 ∧
    0 ≤ (tableEnvelope C).f1 12630 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12630 162 ∧
    0 ≤ (tableEnvelope C).w1 12630 162 ∧ 0 ≤ (tableEnvelope C).w2 12630 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12630 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12630 162 ∧ 0 ≤ d.f1 12630 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12630 162 ∧ 0 ≤ d.w1 12630 162 ∧ 0 ≤ d.w2 12630 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12630 ≤ 2 * (228 / 100 : ℝ) / 12630 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12630 ≤ 2 * (370 / 100 : ℝ) / 12630 := by
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
    (completeRAData (tableEnvelope C) 12630 162).locationBound 12630 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12630 162).energyBound 12630 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12630 162) (d.f1 12630 162) d.f2 ≤
      32 * (((290404239 / 62500000000000000) : ℝ) + (387535093 / 250000000000000000) + (372576813 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12630 162) (d.w1 12630 162)
      (d.w2 12630 162) ≤
      32 * (((465962723 / 25000000000000000000) : ℝ) + (165761789 / 12500000000000000000) + (484521651 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12630 162) (d.f1 12630 162) d.f2 ≤
      ((290404239 / 62500000000000000) : ℝ) ^ 2 + 2 * ((290404239 / 62500000000000000)) * ((387535093 / 250000000000000000)) * (126 / 100) +
      2 * (((387535093 / 250000000000000000)) ^ 2 + 2 * ((290404239 / 62500000000000000)) * ((372576813 / 1000000000000000000))) +
      6 * ((387535093 / 250000000000000000)) * ((372576813 / 1000000000000000000)) * (126 / 100) + 8 * ((372576813 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12630 162) (d.f1 12630 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12630 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12630 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12630 162) (d.f1 12630 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12630 162) (d.w1 12630 162) (d.w2 12630 162)
  have hwexpr0 : 0 ≤ d.w0 12630 162 + d.w1 12630 162 * √(π / 2) +
      2 * d.w2 12630 162 + energyR16 12630 *
      radiusPolynomialRoot16 (d.w0 12630 162) (d.w1 12630 162) (d.w2 12630 162) := by
    positivity
  constructor
  · change (12630 : ℝ) ^ 8 * (mA 12630 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12630 162) (d.f1 12630 162) d.f2 + locationR16 12630 *
        radiusPolynomialRoot16 (d.f0 12630 162) (d.f1 12630 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12630 : ℝ) ^ 8 * (mA 12630 : ℝ) ^ 8 *
        ((((290404239 / 62500000000000000) : ℝ) ^ 2 + 2 * ((290404239 / 62500000000000000)) * ((387535093 / 250000000000000000)) * (126 / 100) +
          2 * (((387535093 / 250000000000000000)) ^ 2 + 2 * ((290404239 / 62500000000000000)) * ((372576813 / 1000000000000000000))) +
          6 * ((387535093 / 250000000000000000)) * ((372576813 / 1000000000000000000)) * (126 / 100) + 8 * ((372576813 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12630) *
          (32 * (((290404239 / 62500000000000000) : ℝ) + (387535093 / 250000000000000000) + (372576813 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12630 : ℝ) ^ 16 *
      (d.w0 12630 162 + d.w1 12630 162 * √(π / 2) + 2 * d.w2 12630 162 +
        energyR16 12630 * radiusPolynomialRoot16 (d.w0 12630 162) (d.w1 12630 162)
          (d.w2 12630 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12630 : ℝ) ^ 16 *
        (((465962723 / 25000000000000000000) : ℝ) + ((165761789 / 12500000000000000000)) * (126 / 100) + 2 * ((484521651 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12630) *
          (32 * (((465962723 / 25000000000000000000) : ℝ) + (165761789 / 12500000000000000000) + (484521651 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12630

/-! A coarse bound on the actual paper statistics constant at dimension 12631. -/
namespace BstLean.Part266.Row12631
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12629 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12629 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12629 128 ≤ (12883 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12883 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12631) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12631 : ℕ))
    (by norm_num : (12631 : ℕ) ≤ 16384)
  have ht : paperTail256 12631 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12631 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12631 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12631 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12631 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12631 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12629 128 * √(2 / (12631 : ℝ)) *
      (√(12631 : ℝ) + paperT0 12631 + paperTail256 12631) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12631 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12631 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12631 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12629 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12629 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12631 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12631

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12631
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12631 (61 / 100) 162 (17 / (100 * 12631)) (26 / (10 * 12631)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12631 (61 / 100) 162 (17 / (100 * 12631)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (242200697 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (19175101 / 12500000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5345193459 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12631 / 12631 * (61 / 100)) ^ 4 * inverseRadius8 (12631 - 1) /
            envelopeGap 12631 (61 / 100) 162 (17 / (100 * 12631)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12631

namespace BstLean.Part266.Row12631
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12631 162 ≤ (2322773657 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12631 162 ≤ (1549833361 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (372503047 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12631 162 ≤ (1863408043 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12631 162 ≤ (662889637 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12631 162 ≤ (121101643 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (242200697 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (242200697 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (19175101 / 12500000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5345193459 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((917161 / 250000000) : ℝ) ≤ √(17 / (100 * 12631) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12631) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2200912071 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7833283041 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12631) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12631) ≤ (55981853 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12631) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12631 * (162 : ℝ) ^ 2 + 26 / (10 * 12631) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12631) : ℝ)) (tA 12631 * 162 ^ 2 + 26 / (10 * 12631)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((917161 / 250000000))) * ((242200697 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((917161 / 250000000)) ^ 3) * ((19175101 / 12500000000000000000000))) + ((5345193459 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((917161 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12631) : ℝ)) d.D d.V d.P (√(tA 12631) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((917161 / 250000000)) ^ 2 * (((2200912071 / 1000000000000000)) * ((7833283041 / 200000000000000000)))) + ((5345193459 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12631) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((917161 / 250000000)) * ((242200697 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12631) : ℝ)) (tA 12631 * 162 ^ 2 + 26 / (10 * 12631)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((242200697 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((917161 / 250000000)) ^ 2) * ((19175101 / 12500000000000000000000)) + ((5345193459 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12631) : ℝ)) (√(26 / (10 * 12631) : ℝ)) d.D d.V d.P (√(tA 12631) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((917161 / 250000000)) * (((2200912071 / 1000000000000000)) * ((7833283041 / 200000000000000000))) + ((5345193459 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12631) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((242200697 / 50000000000000000000) : ℝ) + ((5345193459 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12631

namespace BstLean.Part266.Row12631
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12631 162 ∧
    0 ≤ (tableEnvelope C).f1 12631 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12631 162 ∧
    0 ≤ (tableEnvelope C).w1 12631 162 ∧ 0 ≤ (tableEnvelope C).w2 12631 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12631 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12631 162 ∧ 0 ≤ d.f1 12631 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12631 162 ∧ 0 ≤ d.w1 12631 162 ∧ 0 ≤ d.w2 12631 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12631 ≤ 2 * (228 / 100 : ℝ) / 12631 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12631 ≤ 2 * (370 / 100 : ℝ) / 12631 := by
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
    (completeRAData (tableEnvelope C) 12631 162).locationBound 12631 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12631 162).energyBound 12631 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12631 162) (d.f1 12631 162) d.f2 ≤
      32 * (((2322773657 / 500000000000000000) : ℝ) + (1549833361 / 1000000000000000000) + (372503047 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12631 162) (d.w1 12631 162)
      (d.w2 12631 162) ≤
      32 * (((1863408043 / 100000000000000000000) : ℝ) + (662889637 / 50000000000000000000) + (121101643 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12631 162) (d.f1 12631 162) d.f2 ≤
      ((2322773657 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2322773657 / 500000000000000000)) * ((1549833361 / 1000000000000000000)) * (126 / 100) +
      2 * (((1549833361 / 1000000000000000000)) ^ 2 + 2 * ((2322773657 / 500000000000000000)) * ((372503047 / 1000000000000000000))) +
      6 * ((1549833361 / 1000000000000000000)) * ((372503047 / 1000000000000000000)) * (126 / 100) + 8 * ((372503047 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12631 162) (d.f1 12631 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12631 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12631 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12631 162) (d.f1 12631 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12631 162) (d.w1 12631 162) (d.w2 12631 162)
  have hwexpr0 : 0 ≤ d.w0 12631 162 + d.w1 12631 162 * √(π / 2) +
      2 * d.w2 12631 162 + energyR16 12631 *
      radiusPolynomialRoot16 (d.w0 12631 162) (d.w1 12631 162) (d.w2 12631 162) := by
    positivity
  constructor
  · change (12631 : ℝ) ^ 8 * (mA 12631 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12631 162) (d.f1 12631 162) d.f2 + locationR16 12631 *
        radiusPolynomialRoot16 (d.f0 12631 162) (d.f1 12631 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12631 : ℝ) ^ 8 * (mA 12631 : ℝ) ^ 8 *
        ((((2322773657 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2322773657 / 500000000000000000)) * ((1549833361 / 1000000000000000000)) * (126 / 100) +
          2 * (((1549833361 / 1000000000000000000)) ^ 2 + 2 * ((2322773657 / 500000000000000000)) * ((372503047 / 1000000000000000000))) +
          6 * ((1549833361 / 1000000000000000000)) * ((372503047 / 1000000000000000000)) * (126 / 100) + 8 * ((372503047 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12631) *
          (32 * (((2322773657 / 500000000000000000) : ℝ) + (1549833361 / 1000000000000000000) + (372503047 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12631 : ℝ) ^ 16 *
      (d.w0 12631 162 + d.w1 12631 162 * √(π / 2) + 2 * d.w2 12631 162 +
        energyR16 12631 * radiusPolynomialRoot16 (d.w0 12631 162) (d.w1 12631 162)
          (d.w2 12631 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12631 : ℝ) ^ 16 *
        (((1863408043 / 100000000000000000000) : ℝ) + ((662889637 / 50000000000000000000)) * (126 / 100) + 2 * ((121101643 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12631) *
          (32 * (((1863408043 / 100000000000000000000) : ℝ) + (662889637 / 50000000000000000000) + (121101643 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12631

/-! A coarse bound on the actual paper statistics constant at dimension 12632. -/
namespace BstLean.Part266.Row12632
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12630 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12630 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12630 128 ≤ (12884 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12884 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12632) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12632 : ℕ))
    (by norm_num : (12632 : ℕ) ≤ 16384)
  have ht : paperTail256 12632 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12632 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12632 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12632 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12632 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12632 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12630 128 * √(2 / (12632 : ℝ)) *
      (√(12632 : ℝ) + paperT0 12632 + paperTail256 12632) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12632 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12632 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12632 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12630 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12630 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12632 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12632

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12632
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12632 (61 / 100) 162 (17 / (100 * 12632)) (26 / (10 * 12632)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12632 (61 / 100) 162 (17 / (100 * 12632)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (121071589 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (306704473 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5341776309 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12632 / 12632 * (61 / 100)) ^ 4 * inverseRadius8 (12632 - 1) /
            envelopeGap 12632 (61 / 100) 162 (17 / (100 * 12632)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12632

namespace BstLean.Part266.Row12632
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12632 162 ≤ (4644630777 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12632 162 ≤ (309905459 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (74485881 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12632 162 ≤ (1862966099 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12632 162 ≤ (1325464703 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12632 162 ≤ (484291531 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (121071589 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (121071589 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (306704473 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5341776309 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1834249 / 500000000) : ℝ) ≤ √(17 / (100 * 12632) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12632) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2200650713 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19580107029 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12632) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12632) ≤ (55977421 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12632) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12632 * (162 : ℝ) ^ 2 + 26 / (10 * 12632) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12632) : ℝ)) (tA 12632 * 162 ^ 2 + 26 / (10 * 12632)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1834249 / 500000000))) * ((121071589 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1834249 / 500000000)) ^ 3) * ((306704473 / 200000000000000000000000))) + ((5341776309 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1834249 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12632) : ℝ)) d.D d.V d.P (√(tA 12632) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1834249 / 500000000)) ^ 2 * (((2200650713 / 1000000000000000)) * ((19580107029 / 500000000000000000)))) + ((5341776309 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12632) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1834249 / 500000000)) * ((121071589 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12632) : ℝ)) (tA 12632 * 162 ^ 2 + 26 / (10 * 12632)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((121071589 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1834249 / 500000000)) ^ 2) * ((306704473 / 200000000000000000000000)) + ((5341776309 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12632) : ℝ)) (√(26 / (10 * 12632) : ℝ)) d.D d.V d.P (√(tA 12632) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1834249 / 500000000)) * (((2200650713 / 1000000000000000)) * ((19580107029 / 500000000000000000))) + ((5341776309 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12632) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((121071589 / 25000000000000000000) : ℝ) + ((5341776309 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12632

namespace BstLean.Part266.Row12632
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12632 162 ∧
    0 ≤ (tableEnvelope C).f1 12632 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12632 162 ∧
    0 ≤ (tableEnvelope C).w1 12632 162 ∧ 0 ≤ (tableEnvelope C).w2 12632 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12632 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12632 162 ∧ 0 ≤ d.f1 12632 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12632 162 ∧ 0 ≤ d.w1 12632 162 ∧ 0 ≤ d.w2 12632 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12632 ≤ 2 * (228 / 100 : ℝ) / 12632 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12632 ≤ 2 * (370 / 100 : ℝ) / 12632 := by
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
    (completeRAData (tableEnvelope C) 12632 162).locationBound 12632 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12632 162).energyBound 12632 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12632 162) (d.f1 12632 162) d.f2 ≤
      32 * (((4644630777 / 1000000000000000000) : ℝ) + (309905459 / 200000000000000000) + (74485881 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12632 162) (d.w1 12632 162)
      (d.w2 12632 162) ≤
      32 * (((1862966099 / 100000000000000000000) : ℝ) + (1325464703 / 100000000000000000000) + (484291531 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12632 162) (d.f1 12632 162) d.f2 ≤
      ((4644630777 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4644630777 / 1000000000000000000)) * ((309905459 / 200000000000000000)) * (126 / 100) +
      2 * (((309905459 / 200000000000000000)) ^ 2 + 2 * ((4644630777 / 1000000000000000000)) * ((74485881 / 200000000000000000))) +
      6 * ((309905459 / 200000000000000000)) * ((74485881 / 200000000000000000)) * (126 / 100) + 8 * ((74485881 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12632 162) (d.f1 12632 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12632 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12632 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12632 162) (d.f1 12632 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12632 162) (d.w1 12632 162) (d.w2 12632 162)
  have hwexpr0 : 0 ≤ d.w0 12632 162 + d.w1 12632 162 * √(π / 2) +
      2 * d.w2 12632 162 + energyR16 12632 *
      radiusPolynomialRoot16 (d.w0 12632 162) (d.w1 12632 162) (d.w2 12632 162) := by
    positivity
  constructor
  · change (12632 : ℝ) ^ 8 * (mA 12632 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12632 162) (d.f1 12632 162) d.f2 + locationR16 12632 *
        radiusPolynomialRoot16 (d.f0 12632 162) (d.f1 12632 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12632 : ℝ) ^ 8 * (mA 12632 : ℝ) ^ 8 *
        ((((4644630777 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4644630777 / 1000000000000000000)) * ((309905459 / 200000000000000000)) * (126 / 100) +
          2 * (((309905459 / 200000000000000000)) ^ 2 + 2 * ((4644630777 / 1000000000000000000)) * ((74485881 / 200000000000000000))) +
          6 * ((309905459 / 200000000000000000)) * ((74485881 / 200000000000000000)) * (126 / 100) + 8 * ((74485881 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12632) *
          (32 * (((4644630777 / 1000000000000000000) : ℝ) + (309905459 / 200000000000000000) + (74485881 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12632 : ℝ) ^ 16 *
      (d.w0 12632 162 + d.w1 12632 162 * √(π / 2) + 2 * d.w2 12632 162 +
        energyR16 12632 * radiusPolynomialRoot16 (d.w0 12632 162) (d.w1 12632 162)
          (d.w2 12632 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12632 : ℝ) ^ 16 *
        (((1862966099 / 100000000000000000000) : ℝ) + ((1325464703 / 100000000000000000000)) * (126 / 100) + 2 * ((484291531 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12632) *
          (32 * (((1862966099 / 100000000000000000000) : ℝ) + (1325464703 / 100000000000000000000) + (484291531 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12632

/-! A coarse bound on the actual paper statistics constant at dimension 12633. -/
namespace BstLean.Part266.Row12633
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12631 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12631 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12631 128 ≤ (12885 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12885 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12633) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12633 : ℕ))
    (by norm_num : (12633 : ℕ) ≤ 16384)
  have ht : paperTail256 12633 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12633 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12633 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12633 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12633 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12633 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12631 128 * √(2 / (12633 : ℝ)) *
      (√(12633 : ℝ) + paperT0 12633 + paperTail256 12633) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12633 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12633 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12633 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12631 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12631 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12633 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12633

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12633
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12633 (61 / 100) 162 (17 / (100 * 12633)) (26 / (10 * 12633)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12633 (61 / 100) 162 (17 / (100 * 12633)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (242085677 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1533036843 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5338361619 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12633 / 12633 * (61 / 100)) ^ 4 * inverseRadius8 (12633 - 1) /
            envelopeGap 12633 (61 / 100) 162 (17 / (100 * 12633)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12633

namespace BstLean.Part266.Row12633
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12633 162 ≤ (928742181 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12633 162 ≤ (387305121 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (372355683 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12633 162 ≤ (931261779 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12633 162 ≤ (662574939 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12633 162 ≤ (242088263 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (242085677 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (242085677 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1533036843 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5338361619 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3668353 / 1000000000) : ℝ) ≤ √(17 / (100 * 12633) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12633) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2200389407 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4894251799 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12633) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12633) ≤ (5597299 / 50000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12633) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12633 * (162 : ℝ) ^ 2 + 26 / (10 * 12633) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12633) : ℝ)) (tA 12633 * 162 ^ 2 + 26 / (10 * 12633)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3668353 / 1000000000))) * ((242085677 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3668353 / 1000000000)) ^ 3) * ((1533036843 / 1000000000000000000000000))) + ((5338361619 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3668353 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12633) : ℝ)) d.D d.V d.P (√(tA 12633) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3668353 / 1000000000)) ^ 2 * (((2200389407 / 1000000000000000)) * ((4894251799 / 125000000000000000)))) + ((5338361619 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12633) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3668353 / 1000000000)) * ((242085677 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12633) : ℝ)) (tA 12633 * 162 ^ 2 + 26 / (10 * 12633)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((242085677 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3668353 / 1000000000)) ^ 2) * ((1533036843 / 1000000000000000000000000)) + ((5338361619 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12633) : ℝ)) (√(26 / (10 * 12633) : ℝ)) d.D d.V d.P (√(tA 12633) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3668353 / 1000000000)) * (((2200389407 / 1000000000000000)) * ((4894251799 / 125000000000000000))) + ((5338361619 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12633) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((242085677 / 50000000000000000000) : ℝ) + ((5338361619 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12633

namespace BstLean.Part266.Row12633
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12633 162 ∧
    0 ≤ (tableEnvelope C).f1 12633 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12633 162 ∧
    0 ≤ (tableEnvelope C).w1 12633 162 ∧ 0 ≤ (tableEnvelope C).w2 12633 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12633 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12633 162 ∧ 0 ≤ d.f1 12633 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12633 162 ∧ 0 ≤ d.w1 12633 162 ∧ 0 ≤ d.w2 12633 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12633 ≤ 2 * (228 / 100 : ℝ) / 12633 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12633 ≤ 2 * (370 / 100 : ℝ) / 12633 := by
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
    (completeRAData (tableEnvelope C) 12633 162).locationBound 12633 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12633 162).energyBound 12633 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12633 162) (d.f1 12633 162) d.f2 ≤
      32 * (((928742181 / 200000000000000000) : ℝ) + (387305121 / 250000000000000000) + (372355683 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12633 162) (d.w1 12633 162)
      (d.w2 12633 162) ≤
      32 * (((931261779 / 50000000000000000000) : ℝ) + (662574939 / 50000000000000000000) + (242088263 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12633 162) (d.f1 12633 162) d.f2 ≤
      ((928742181 / 200000000000000000) : ℝ) ^ 2 + 2 * ((928742181 / 200000000000000000)) * ((387305121 / 250000000000000000)) * (126 / 100) +
      2 * (((387305121 / 250000000000000000)) ^ 2 + 2 * ((928742181 / 200000000000000000)) * ((372355683 / 1000000000000000000))) +
      6 * ((387305121 / 250000000000000000)) * ((372355683 / 1000000000000000000)) * (126 / 100) + 8 * ((372355683 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12633 162) (d.f1 12633 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12633 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12633 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12633 162) (d.f1 12633 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12633 162) (d.w1 12633 162) (d.w2 12633 162)
  have hwexpr0 : 0 ≤ d.w0 12633 162 + d.w1 12633 162 * √(π / 2) +
      2 * d.w2 12633 162 + energyR16 12633 *
      radiusPolynomialRoot16 (d.w0 12633 162) (d.w1 12633 162) (d.w2 12633 162) := by
    positivity
  constructor
  · change (12633 : ℝ) ^ 8 * (mA 12633 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12633 162) (d.f1 12633 162) d.f2 + locationR16 12633 *
        radiusPolynomialRoot16 (d.f0 12633 162) (d.f1 12633 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12633 : ℝ) ^ 8 * (mA 12633 : ℝ) ^ 8 *
        ((((928742181 / 200000000000000000) : ℝ) ^ 2 + 2 * ((928742181 / 200000000000000000)) * ((387305121 / 250000000000000000)) * (126 / 100) +
          2 * (((387305121 / 250000000000000000)) ^ 2 + 2 * ((928742181 / 200000000000000000)) * ((372355683 / 1000000000000000000))) +
          6 * ((387305121 / 250000000000000000)) * ((372355683 / 1000000000000000000)) * (126 / 100) + 8 * ((372355683 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12633) *
          (32 * (((928742181 / 200000000000000000) : ℝ) + (387305121 / 250000000000000000) + (372355683 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12633 : ℝ) ^ 16 *
      (d.w0 12633 162 + d.w1 12633 162 * √(π / 2) + 2 * d.w2 12633 162 +
        energyR16 12633 * radiusPolynomialRoot16 (d.w0 12633 162) (d.w1 12633 162)
          (d.w2 12633 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12633 : ℝ) ^ 16 *
        (((931261779 / 50000000000000000000) : ℝ) + ((662574939 / 50000000000000000000)) * (126 / 100) + 2 * ((242088263 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12633) *
          (32 * (((931261779 / 50000000000000000000) : ℝ) + (662574939 / 50000000000000000000) + (242088263 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12633

/-! A coarse bound on the actual paper statistics constant at dimension 12634. -/
namespace BstLean.Part266.Row12634
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12632 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12632 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12632 128 ≤ (12886 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12886 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12634) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12634 : ℕ))
    (by norm_num : (12634 : ℕ) ≤ 16384)
  have ht : paperTail256 12634 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12634 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12634 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12634 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12634 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12634 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12632 128 * √(2 / (12634 : ℝ)) *
      (√(12634 : ℝ) + paperT0 12634 + paperTail256 12634) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12634 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12634 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12634 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12632 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12632 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12634 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12634

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12634
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12634 (61 / 100) 162 (17 / (100 * 12634)) (26 / (10 * 12634)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12634 (61 / 100) 162 (17 / (100 * 12634)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (121014097 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1532551513 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1333737347 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12634 / 12634 * (61 / 100)) ^ 4 * inverseRadius8 (12634 - 1) /
            envelopeGap 12634 (61 / 100) 162 (17 / (100 * 12634)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12634

namespace BstLean.Part266.Row12634
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12634 162 ≤ (4642791349 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12634 162 ≤ (1548913771 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (186140991 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12634 162 ≤ (116380073 / 6250000000000000000)
  w1 : (tableEnvelope C).w1 12634 162 ≤ (1324835157 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12634 162 ≤ (121015389 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (121014097 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (121014097 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1532551513 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1333737347 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((229263 / 62500000) : ℝ) ≤ √(17 / (100 * 12634) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12634) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2200128151 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19573908099 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12634) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12634) ≤ (699607 / 6250000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12634) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12634 * (162 : ℝ) ^ 2 + 26 / (10 * 12634) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12634) : ℝ)) (tA 12634 * 162 ^ 2 + 26 / (10 * 12634)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((229263 / 62500000))) * ((121014097 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((229263 / 62500000)) ^ 3) * ((1532551513 / 1000000000000000000000000))) + ((1333737347 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((229263 / 62500000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12634) : ℝ)) d.D d.V d.P (√(tA 12634) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((229263 / 62500000)) ^ 2 * (((2200128151 / 1000000000000000)) * ((19573908099 / 500000000000000000)))) + ((1333737347 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12634) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((229263 / 62500000)) * ((121014097 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12634) : ℝ)) (tA 12634 * 162 ^ 2 + 26 / (10 * 12634)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((121014097 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((229263 / 62500000)) ^ 2) * ((1532551513 / 1000000000000000000000000)) + ((1333737347 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12634) : ℝ)) (√(26 / (10 * 12634) : ℝ)) d.D d.V d.P (√(tA 12634) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((229263 / 62500000)) * (((2200128151 / 1000000000000000)) * ((19573908099 / 500000000000000000))) + ((1333737347 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12634) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((121014097 / 25000000000000000000) : ℝ) + ((1333737347 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12634

namespace BstLean.Part266.Row12634
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12634 162 ∧
    0 ≤ (tableEnvelope C).f1 12634 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12634 162 ∧
    0 ≤ (tableEnvelope C).w1 12634 162 ∧ 0 ≤ (tableEnvelope C).w2 12634 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12634 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12634 162 ∧ 0 ≤ d.f1 12634 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12634 162 ∧ 0 ≤ d.w1 12634 162 ∧ 0 ≤ d.w2 12634 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12634 ≤ 2 * (228 / 100 : ℝ) / 12634 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12634 ≤ 2 * (370 / 100 : ℝ) / 12634 := by
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
    (completeRAData (tableEnvelope C) 12634 162).locationBound 12634 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12634 162).energyBound 12634 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12634 162) (d.f1 12634 162) d.f2 ≤
      32 * (((4642791349 / 1000000000000000000) : ℝ) + (1548913771 / 1000000000000000000) + (186140991 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12634 162) (d.w1 12634 162)
      (d.w2 12634 162) ≤
      32 * (((116380073 / 6250000000000000000) : ℝ) + (1324835157 / 100000000000000000000) + (121015389 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12634 162) (d.f1 12634 162) d.f2 ≤
      ((4642791349 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4642791349 / 1000000000000000000)) * ((1548913771 / 1000000000000000000)) * (126 / 100) +
      2 * (((1548913771 / 1000000000000000000)) ^ 2 + 2 * ((4642791349 / 1000000000000000000)) * ((186140991 / 500000000000000000))) +
      6 * ((1548913771 / 1000000000000000000)) * ((186140991 / 500000000000000000)) * (126 / 100) + 8 * ((186140991 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12634 162) (d.f1 12634 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12634 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12634 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12634 162) (d.f1 12634 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12634 162) (d.w1 12634 162) (d.w2 12634 162)
  have hwexpr0 : 0 ≤ d.w0 12634 162 + d.w1 12634 162 * √(π / 2) +
      2 * d.w2 12634 162 + energyR16 12634 *
      radiusPolynomialRoot16 (d.w0 12634 162) (d.w1 12634 162) (d.w2 12634 162) := by
    positivity
  constructor
  · change (12634 : ℝ) ^ 8 * (mA 12634 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12634 162) (d.f1 12634 162) d.f2 + locationR16 12634 *
        radiusPolynomialRoot16 (d.f0 12634 162) (d.f1 12634 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12634 : ℝ) ^ 8 * (mA 12634 : ℝ) ^ 8 *
        ((((4642791349 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4642791349 / 1000000000000000000)) * ((1548913771 / 1000000000000000000)) * (126 / 100) +
          2 * (((1548913771 / 1000000000000000000)) ^ 2 + 2 * ((4642791349 / 1000000000000000000)) * ((186140991 / 500000000000000000))) +
          6 * ((1548913771 / 1000000000000000000)) * ((186140991 / 500000000000000000)) * (126 / 100) + 8 * ((186140991 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12634) *
          (32 * (((4642791349 / 1000000000000000000) : ℝ) + (1548913771 / 1000000000000000000) + (186140991 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12634 : ℝ) ^ 16 *
      (d.w0 12634 162 + d.w1 12634 162 * √(π / 2) + 2 * d.w2 12634 162 +
        energyR16 12634 * radiusPolynomialRoot16 (d.w0 12634 162) (d.w1 12634 162)
          (d.w2 12634 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12634 : ℝ) ^ 16 *
        (((116380073 / 6250000000000000000) : ℝ) + ((1324835157 / 100000000000000000000)) * (126 / 100) + 2 * ((121015389 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12634) *
          (32 * (((116380073 / 6250000000000000000) : ℝ) + (1324835157 / 100000000000000000000) + (121015389 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12634

/-! A coarse bound on the actual paper statistics constant at dimension 12635. -/
namespace BstLean.Part266.Row12635
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12633 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12633 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12633 128 ≤ (12887 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12887 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12635) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12635 : ℕ))
    (by norm_num : (12635 : ℕ) ≤ 16384)
  have ht : paperTail256 12635 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12635 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12635 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12635 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12635 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12635 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12633 128 * √(2 / (12635 : ℝ)) *
      (√(12635 : ℝ) + paperT0 12635 + paperTail256 12635) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12635 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12635 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12635 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12633 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12633 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12635 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12635

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12635
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12635 (61 / 100) 162 (17 / (100 * 12635)) (26 / (10 * 12635)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12635 (61 / 100) 162 (17 / (100 * 12635)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (483941459 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (766033187 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1332884903 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12635 / 12635 * (61 / 100)) ^ 4 * inverseRadius8 (12635 - 1) /
            envelopeGap 12635 (61 / 100) 162 (17 / (100 * 12635)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12635

namespace BstLean.Part266.Row12635
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12635 162 ≤ (4641872109 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12635 162 ≤ (1548607159 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (74441661 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12635 162 ≤ (465409733 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12635 162 ≤ (1324520543 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12635 162 ≤ (3780833 / 781250000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (483941459 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (483941459 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (766033187 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1332884903 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3668063 / 1000000000) : ℝ) ≤ √(17 / (100 * 12635) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12635) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2199866949 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39141619461 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12635) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12635) ≤ (5596413 / 50000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12635) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12635 * (162 : ℝ) ^ 2 + 26 / (10 * 12635) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12635) : ℝ)) (tA 12635 * 162 ^ 2 + 26 / (10 * 12635)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3668063 / 1000000000))) * ((483941459 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3668063 / 1000000000)) ^ 3) * ((766033187 / 500000000000000000000000))) + ((1332884903 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3668063 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12635) : ℝ)) d.D d.V d.P (√(tA 12635) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3668063 / 1000000000)) ^ 2 * (((2199866949 / 1000000000000000)) * ((39141619461 / 1000000000000000000)))) + ((1332884903 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12635) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3668063 / 1000000000)) * ((483941459 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12635) : ℝ)) (tA 12635 * 162 ^ 2 + 26 / (10 * 12635)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((483941459 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3668063 / 1000000000)) ^ 2) * ((766033187 / 500000000000000000000000)) + ((1332884903 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12635) : ℝ)) (√(26 / (10 * 12635) : ℝ)) d.D d.V d.P (√(tA 12635) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3668063 / 1000000000)) * (((2199866949 / 1000000000000000)) * ((39141619461 / 1000000000000000000))) + ((1332884903 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12635) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((483941459 / 100000000000000000000) : ℝ) + ((1332884903 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12635

namespace BstLean.Part266.Row12635
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12635 162 ∧
    0 ≤ (tableEnvelope C).f1 12635 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12635 162 ∧
    0 ≤ (tableEnvelope C).w1 12635 162 ∧ 0 ≤ (tableEnvelope C).w2 12635 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12635 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12635 162 ∧ 0 ≤ d.f1 12635 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12635 162 ∧ 0 ≤ d.w1 12635 162 ∧ 0 ≤ d.w2 12635 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12635 ≤ 2 * (228 / 100 : ℝ) / 12635 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12635 ≤ 2 * (370 / 100 : ℝ) / 12635 := by
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
    (completeRAData (tableEnvelope C) 12635 162).locationBound 12635 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12635 162).energyBound 12635 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12635 162) (d.f1 12635 162) d.f2 ≤
      32 * (((4641872109 / 1000000000000000000) : ℝ) + (1548607159 / 1000000000000000000) + (74441661 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12635 162) (d.w1 12635 162)
      (d.w2 12635 162) ≤
      32 * (((465409733 / 25000000000000000000) : ℝ) + (1324520543 / 100000000000000000000) + (3780833 / 781250000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12635 162) (d.f1 12635 162) d.f2 ≤
      ((4641872109 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4641872109 / 1000000000000000000)) * ((1548607159 / 1000000000000000000)) * (126 / 100) +
      2 * (((1548607159 / 1000000000000000000)) ^ 2 + 2 * ((4641872109 / 1000000000000000000)) * ((74441661 / 200000000000000000))) +
      6 * ((1548607159 / 1000000000000000000)) * ((74441661 / 200000000000000000)) * (126 / 100) + 8 * ((74441661 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12635 162) (d.f1 12635 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12635 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12635 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12635 162) (d.f1 12635 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12635 162) (d.w1 12635 162) (d.w2 12635 162)
  have hwexpr0 : 0 ≤ d.w0 12635 162 + d.w1 12635 162 * √(π / 2) +
      2 * d.w2 12635 162 + energyR16 12635 *
      radiusPolynomialRoot16 (d.w0 12635 162) (d.w1 12635 162) (d.w2 12635 162) := by
    positivity
  constructor
  · change (12635 : ℝ) ^ 8 * (mA 12635 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12635 162) (d.f1 12635 162) d.f2 + locationR16 12635 *
        radiusPolynomialRoot16 (d.f0 12635 162) (d.f1 12635 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12635 : ℝ) ^ 8 * (mA 12635 : ℝ) ^ 8 *
        ((((4641872109 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4641872109 / 1000000000000000000)) * ((1548607159 / 1000000000000000000)) * (126 / 100) +
          2 * (((1548607159 / 1000000000000000000)) ^ 2 + 2 * ((4641872109 / 1000000000000000000)) * ((74441661 / 200000000000000000))) +
          6 * ((1548607159 / 1000000000000000000)) * ((74441661 / 200000000000000000)) * (126 / 100) + 8 * ((74441661 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12635) *
          (32 * (((4641872109 / 1000000000000000000) : ℝ) + (1548607159 / 1000000000000000000) + (74441661 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12635 : ℝ) ^ 16 *
      (d.w0 12635 162 + d.w1 12635 162 * √(π / 2) + 2 * d.w2 12635 162 +
        energyR16 12635 * radiusPolynomialRoot16 (d.w0 12635 162) (d.w1 12635 162)
          (d.w2 12635 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12635 : ℝ) ^ 16 *
        (((465409733 / 25000000000000000000) : ℝ) + ((1324520543 / 100000000000000000000)) * (126 / 100) + 2 * ((3780833 / 781250000000000000)) +
          (2 * (370 / 100 : ℝ) / 12635) *
          (32 * (((465409733 / 25000000000000000000) : ℝ) + (1324520543 / 100000000000000000000) + (3780833 / 781250000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12635

/-! A coarse bound on the actual paper statistics constant at dimension 12636. -/
namespace BstLean.Part266.Row12636
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12634 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12634 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12634 128 ≤ (12888 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12888 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12636) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12636 : ℕ))
    (by norm_num : (12636 : ℕ) ≤ 16384)
  have ht : paperTail256 12636 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12636 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12636 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12636 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12636 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12636 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12634 128 * √(2 / (12636 : ℝ)) *
      (√(12636 : ℝ) + paperT0 12636 + paperTail256 12636) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12636 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12636 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12636 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12634 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12634 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12636 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12636

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12636
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12636 (61 / 100) 162 (17 / (100 * 12636)) (26 / (10 * 12636)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12636 (61 / 100) 162 (17 / (100 * 12636)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (241913283 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (382895357 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (532813229 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12636 / 12636 * (61 / 100)) ^ 4 * inverseRadius8 (12636 - 1) /
            envelopeGap 12636 (61 / 100) 162 (17 / (100 * 12636)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12636

namespace BstLean.Part266.Row12636
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12636 162 ≤ (4640953189 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12636 162 ≤ (774150323 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (372134649 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12636 162 ≤ (116324803 / 6250000000000000000)
  w1 : (tableEnvelope C).w1 12636 162 ≤ (264841207 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12636 162 ≤ (30239483 / 6250000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (241913283 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (241913283 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (382895357 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (532813229 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1833959 / 500000000) : ℝ) ≤ √(17 / (100 * 12636) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12636) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2199605797 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39135424209 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12636) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12636) ≤ (55959701 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12636) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12636 * (162 : ℝ) ^ 2 + 26 / (10 * 12636) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12636) : ℝ)) (tA 12636 * 162 ^ 2 + 26 / (10 * 12636)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1833959 / 500000000))) * ((241913283 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1833959 / 500000000)) ^ 3) * ((382895357 / 250000000000000000000000))) + ((532813229 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1833959 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12636) : ℝ)) d.D d.V d.P (√(tA 12636) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1833959 / 500000000)) ^ 2 * (((2199605797 / 1000000000000000)) * ((39135424209 / 1000000000000000000)))) + ((532813229 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12636) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1833959 / 500000000)) * ((241913283 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12636) : ℝ)) (tA 12636 * 162 ^ 2 + 26 / (10 * 12636)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((241913283 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1833959 / 500000000)) ^ 2) * ((382895357 / 250000000000000000000000)) + ((532813229 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12636) : ℝ)) (√(26 / (10 * 12636) : ℝ)) d.D d.V d.P (√(tA 12636) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1833959 / 500000000)) * (((2199605797 / 1000000000000000)) * ((39135424209 / 1000000000000000000))) + ((532813229 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12636) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((241913283 / 50000000000000000000) : ℝ) + ((532813229 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12636

namespace BstLean.Part266.Row12636
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12636 162 ∧
    0 ≤ (tableEnvelope C).f1 12636 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12636 162 ∧
    0 ≤ (tableEnvelope C).w1 12636 162 ∧ 0 ≤ (tableEnvelope C).w2 12636 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12636 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12636 162 ∧ 0 ≤ d.f1 12636 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12636 162 ∧ 0 ≤ d.w1 12636 162 ∧ 0 ≤ d.w2 12636 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12636 ≤ 2 * (228 / 100 : ℝ) / 12636 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12636 ≤ 2 * (370 / 100 : ℝ) / 12636 := by
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
    (completeRAData (tableEnvelope C) 12636 162).locationBound 12636 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12636 162).energyBound 12636 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12636 162) (d.f1 12636 162) d.f2 ≤
      32 * (((4640953189 / 1000000000000000000) : ℝ) + (774150323 / 500000000000000000) + (372134649 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12636 162) (d.w1 12636 162)
      (d.w2 12636 162) ≤
      32 * (((116324803 / 6250000000000000000) : ℝ) + (264841207 / 20000000000000000000) + (30239483 / 6250000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12636 162) (d.f1 12636 162) d.f2 ≤
      ((4640953189 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4640953189 / 1000000000000000000)) * ((774150323 / 500000000000000000)) * (126 / 100) +
      2 * (((774150323 / 500000000000000000)) ^ 2 + 2 * ((4640953189 / 1000000000000000000)) * ((372134649 / 1000000000000000000))) +
      6 * ((774150323 / 500000000000000000)) * ((372134649 / 1000000000000000000)) * (126 / 100) + 8 * ((372134649 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12636 162) (d.f1 12636 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12636 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12636 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12636 162) (d.f1 12636 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12636 162) (d.w1 12636 162) (d.w2 12636 162)
  have hwexpr0 : 0 ≤ d.w0 12636 162 + d.w1 12636 162 * √(π / 2) +
      2 * d.w2 12636 162 + energyR16 12636 *
      radiusPolynomialRoot16 (d.w0 12636 162) (d.w1 12636 162) (d.w2 12636 162) := by
    positivity
  constructor
  · change (12636 : ℝ) ^ 8 * (mA 12636 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12636 162) (d.f1 12636 162) d.f2 + locationR16 12636 *
        radiusPolynomialRoot16 (d.f0 12636 162) (d.f1 12636 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12636 : ℝ) ^ 8 * (mA 12636 : ℝ) ^ 8 *
        ((((4640953189 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4640953189 / 1000000000000000000)) * ((774150323 / 500000000000000000)) * (126 / 100) +
          2 * (((774150323 / 500000000000000000)) ^ 2 + 2 * ((4640953189 / 1000000000000000000)) * ((372134649 / 1000000000000000000))) +
          6 * ((774150323 / 500000000000000000)) * ((372134649 / 1000000000000000000)) * (126 / 100) + 8 * ((372134649 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12636) *
          (32 * (((4640953189 / 1000000000000000000) : ℝ) + (774150323 / 500000000000000000) + (372134649 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12636 : ℝ) ^ 16 *
      (d.w0 12636 162 + d.w1 12636 162 * √(π / 2) + 2 * d.w2 12636 162 +
        energyR16 12636 * radiusPolynomialRoot16 (d.w0 12636 162) (d.w1 12636 162)
          (d.w2 12636 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12636 : ℝ) ^ 16 *
        (((116324803 / 6250000000000000000) : ℝ) + ((264841207 / 20000000000000000000)) * (126 / 100) + 2 * ((30239483 / 6250000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12636) *
          (32 * (((116324803 / 6250000000000000000) : ℝ) + (264841207 / 20000000000000000000) + (30239483 / 6250000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12636

/-! A coarse bound on the actual paper statistics constant at dimension 12637. -/
namespace BstLean.Part266.Row12637
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12635 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12635 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12635 128 ≤ (12889 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12889 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12637) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12637 : ℕ))
    (by norm_num : (12637 : ℕ) ≤ 16384)
  have ht : paperTail256 12637 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12637 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12637 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12637 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12637 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12637 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12635 128 * √(2 / (12637 : ℝ)) *
      (√(12637 : ℝ) + paperT0 12637 + paperTail256 12637) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12637 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12637 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12637 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12635 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12635 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12637 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12637

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12637
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12637 (61 / 100) 162 (17 / (100 * 12637)) (26 / (10 * 12637)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12637 (61 / 100) 162 (17 / (100 * 12637)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (48371171 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (765548337 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5324727421 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12637 / 12637 * (61 / 100)) ^ 4 * inverseRadius8 (12637 - 1) /
            envelopeGap 12637 (61 / 100) 162 (17 / (100 * 12637)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12637

namespace BstLean.Part266.Row12637
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12637 162 ≤ (1160008647 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12637 162 ≤ (773997117 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (46507627 / 125000000000000000)
  w0 : (tableEnvelope C).w0 12637 162 ≤ (1860754919 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12637 162 ≤ (1323891633 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12637 162 ≤ (120929217 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (48371171 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (48371171 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (765548337 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5324727421 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3667773 / 1000000000) : ℝ) ≤ √(17 / (100 * 12637) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12637) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1099672349 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3912923043 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12637) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12637) ≤ (55955273 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12637) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12637 * (162 : ℝ) ^ 2 + 26 / (10 * 12637) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12637) : ℝ)) (tA 12637 * 162 ^ 2 + 26 / (10 * 12637)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3667773 / 1000000000))) * ((48371171 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3667773 / 1000000000)) ^ 3) * ((765548337 / 500000000000000000000000))) + ((5324727421 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3667773 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12637) : ℝ)) d.D d.V d.P (√(tA 12637) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3667773 / 1000000000)) ^ 2 * (((1099672349 / 500000000000000)) * ((3912923043 / 100000000000000000)))) + ((5324727421 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12637) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3667773 / 1000000000)) * ((48371171 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12637) : ℝ)) (tA 12637 * 162 ^ 2 + 26 / (10 * 12637)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((48371171 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3667773 / 1000000000)) ^ 2) * ((765548337 / 500000000000000000000000)) + ((5324727421 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12637) : ℝ)) (√(26 / (10 * 12637) : ℝ)) d.D d.V d.P (√(tA 12637) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3667773 / 1000000000)) * (((1099672349 / 500000000000000)) * ((3912923043 / 100000000000000000))) + ((5324727421 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12637) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((48371171 / 10000000000000000000) : ℝ) + ((5324727421 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12637

namespace BstLean.Part266.Row12637
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12637 162 ∧
    0 ≤ (tableEnvelope C).f1 12637 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12637 162 ∧
    0 ≤ (tableEnvelope C).w1 12637 162 ∧ 0 ≤ (tableEnvelope C).w2 12637 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12637 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12637 162 ∧ 0 ≤ d.f1 12637 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12637 162 ∧ 0 ≤ d.w1 12637 162 ∧ 0 ≤ d.w2 12637 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12637 ≤ 2 * (228 / 100 : ℝ) / 12637 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12637 ≤ 2 * (370 / 100 : ℝ) / 12637 := by
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
    (completeRAData (tableEnvelope C) 12637 162).locationBound 12637 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12637 162).energyBound 12637 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12637 162) (d.f1 12637 162) d.f2 ≤
      32 * (((1160008647 / 250000000000000000) : ℝ) + (773997117 / 500000000000000000) + (46507627 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12637 162) (d.w1 12637 162)
      (d.w2 12637 162) ≤
      32 * (((1860754919 / 100000000000000000000) : ℝ) + (1323891633 / 100000000000000000000) + (120929217 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12637 162) (d.f1 12637 162) d.f2 ≤
      ((1160008647 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1160008647 / 250000000000000000)) * ((773997117 / 500000000000000000)) * (126 / 100) +
      2 * (((773997117 / 500000000000000000)) ^ 2 + 2 * ((1160008647 / 250000000000000000)) * ((46507627 / 125000000000000000))) +
      6 * ((773997117 / 500000000000000000)) * ((46507627 / 125000000000000000)) * (126 / 100) + 8 * ((46507627 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12637 162) (d.f1 12637 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12637 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12637 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12637 162) (d.f1 12637 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12637 162) (d.w1 12637 162) (d.w2 12637 162)
  have hwexpr0 : 0 ≤ d.w0 12637 162 + d.w1 12637 162 * √(π / 2) +
      2 * d.w2 12637 162 + energyR16 12637 *
      radiusPolynomialRoot16 (d.w0 12637 162) (d.w1 12637 162) (d.w2 12637 162) := by
    positivity
  constructor
  · change (12637 : ℝ) ^ 8 * (mA 12637 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12637 162) (d.f1 12637 162) d.f2 + locationR16 12637 *
        radiusPolynomialRoot16 (d.f0 12637 162) (d.f1 12637 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12637 : ℝ) ^ 8 * (mA 12637 : ℝ) ^ 8 *
        ((((1160008647 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1160008647 / 250000000000000000)) * ((773997117 / 500000000000000000)) * (126 / 100) +
          2 * (((773997117 / 500000000000000000)) ^ 2 + 2 * ((1160008647 / 250000000000000000)) * ((46507627 / 125000000000000000))) +
          6 * ((773997117 / 500000000000000000)) * ((46507627 / 125000000000000000)) * (126 / 100) + 8 * ((46507627 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12637) *
          (32 * (((1160008647 / 250000000000000000) : ℝ) + (773997117 / 500000000000000000) + (46507627 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12637 : ℝ) ^ 16 *
      (d.w0 12637 162 + d.w1 12637 162 * √(π / 2) + 2 * d.w2 12637 162 +
        energyR16 12637 * radiusPolynomialRoot16 (d.w0 12637 162) (d.w1 12637 162)
          (d.w2 12637 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12637 : ℝ) ^ 16 *
        (((1860754919 / 100000000000000000000) : ℝ) + ((1323891633 / 100000000000000000000)) * (126 / 100) + 2 * ((120929217 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12637) *
          (32 * (((1860754919 / 100000000000000000000) : ℝ) + (1323891633 / 100000000000000000000) + (120929217 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12637

/-! A coarse bound on the actual paper statistics constant at dimension 12638. -/
namespace BstLean.Part266.Row12638
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12636 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12636 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12636 128 ≤ (12890 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12890 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12638) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12638 : ℕ))
    (by norm_num : (12638 : ℕ) ≤ 16384)
  have ht : paperTail256 12638 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12638 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12638 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12638 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12638 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12638 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12636 128 * √(2 / (12638 : ℝ)) *
      (√(12638 : ℝ) + paperT0 12638 + paperTail256 12638) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12638 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12638 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12638 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12636 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12636 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12638 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12638

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12638
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12638 (61 / 100) 162 (17 / (100 * 12638)) (26 / (10 * 12638)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12638 (61 / 100) 162 (17 / (100 * 12638)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (48359689 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1530612111 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2660662501 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12638 / 12638 * (61 / 100)) ^ 4 * inverseRadius8 (12638 - 1) /
            envelopeGap 12638 (61 / 100) 162 (17 / (100 * 12638)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12638

namespace BstLean.Part266.Row12638
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12638 162 ≤ (4639116301 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12638 162 ≤ (19346099 / 12500000000000000)
  f2 : (tableEnvelope C).f2 ≤ (74397481 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12638 162 ≤ (1860313141 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12638 162 ≤ (165447167 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 12638 162 ≤ (96720409 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (48359689 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (48359689 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1530612111 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2660662501 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((916907 / 250000000) : ℝ) ≤ √(17 / (100 * 12638) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12638) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2199083651 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39123038111 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12638) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12638) ≤ (111901691 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12638) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12638 * (162 : ℝ) ^ 2 + 26 / (10 * 12638) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12638) : ℝ)) (tA 12638 * 162 ^ 2 + 26 / (10 * 12638)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((916907 / 250000000))) * ((48359689 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((916907 / 250000000)) ^ 3) * ((1530612111 / 1000000000000000000000000))) + ((2660662501 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((916907 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12638) : ℝ)) d.D d.V d.P (√(tA 12638) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((916907 / 250000000)) ^ 2 * (((2199083651 / 1000000000000000)) * ((39123038111 / 1000000000000000000)))) + ((2660662501 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12638) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((916907 / 250000000)) * ((48359689 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12638) : ℝ)) (tA 12638 * 162 ^ 2 + 26 / (10 * 12638)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((48359689 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((916907 / 250000000)) ^ 2) * ((1530612111 / 1000000000000000000000000)) + ((2660662501 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12638) : ℝ)) (√(26 / (10 * 12638) : ℝ)) d.D d.V d.P (√(tA 12638) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((916907 / 250000000)) * (((2199083651 / 1000000000000000)) * ((39123038111 / 1000000000000000000))) + ((2660662501 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12638) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((48359689 / 10000000000000000000) : ℝ) + ((2660662501 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12638

namespace BstLean.Part266.Row12638
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12638 162 ∧
    0 ≤ (tableEnvelope C).f1 12638 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12638 162 ∧
    0 ≤ (tableEnvelope C).w1 12638 162 ∧ 0 ≤ (tableEnvelope C).w2 12638 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12638 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12638 162 ∧ 0 ≤ d.f1 12638 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12638 162 ∧ 0 ≤ d.w1 12638 162 ∧ 0 ≤ d.w2 12638 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12638 ≤ 2 * (228 / 100 : ℝ) / 12638 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12638 ≤ 2 * (370 / 100 : ℝ) / 12638 := by
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
    (completeRAData (tableEnvelope C) 12638 162).locationBound 12638 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12638 162).energyBound 12638 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12638 162) (d.f1 12638 162) d.f2 ≤
      32 * (((4639116301 / 1000000000000000000) : ℝ) + (19346099 / 12500000000000000) + (74397481 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12638 162) (d.w1 12638 162)
      (d.w2 12638 162) ≤
      32 * (((1860313141 / 100000000000000000000) : ℝ) + (165447167 / 12500000000000000000) + (96720409 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12638 162) (d.f1 12638 162) d.f2 ≤
      ((4639116301 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4639116301 / 1000000000000000000)) * ((19346099 / 12500000000000000)) * (126 / 100) +
      2 * (((19346099 / 12500000000000000)) ^ 2 + 2 * ((4639116301 / 1000000000000000000)) * ((74397481 / 200000000000000000))) +
      6 * ((19346099 / 12500000000000000)) * ((74397481 / 200000000000000000)) * (126 / 100) + 8 * ((74397481 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12638 162) (d.f1 12638 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12638 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12638 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12638 162) (d.f1 12638 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12638 162) (d.w1 12638 162) (d.w2 12638 162)
  have hwexpr0 : 0 ≤ d.w0 12638 162 + d.w1 12638 162 * √(π / 2) +
      2 * d.w2 12638 162 + energyR16 12638 *
      radiusPolynomialRoot16 (d.w0 12638 162) (d.w1 12638 162) (d.w2 12638 162) := by
    positivity
  constructor
  · change (12638 : ℝ) ^ 8 * (mA 12638 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12638 162) (d.f1 12638 162) d.f2 + locationR16 12638 *
        radiusPolynomialRoot16 (d.f0 12638 162) (d.f1 12638 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12638 : ℝ) ^ 8 * (mA 12638 : ℝ) ^ 8 *
        ((((4639116301 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4639116301 / 1000000000000000000)) * ((19346099 / 12500000000000000)) * (126 / 100) +
          2 * (((19346099 / 12500000000000000)) ^ 2 + 2 * ((4639116301 / 1000000000000000000)) * ((74397481 / 200000000000000000))) +
          6 * ((19346099 / 12500000000000000)) * ((74397481 / 200000000000000000)) * (126 / 100) + 8 * ((74397481 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12638) *
          (32 * (((4639116301 / 1000000000000000000) : ℝ) + (19346099 / 12500000000000000) + (74397481 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12638 : ℝ) ^ 16 *
      (d.w0 12638 162 + d.w1 12638 162 * √(π / 2) + 2 * d.w2 12638 162 +
        energyR16 12638 * radiusPolynomialRoot16 (d.w0 12638 162) (d.w1 12638 162)
          (d.w2 12638 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12638 : ℝ) ^ 16 *
        (((1860313141 / 100000000000000000000) : ℝ) + ((165447167 / 12500000000000000000)) * (126 / 100) + 2 * ((96720409 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12638) *
          (32 * (((1860313141 / 100000000000000000000) : ℝ) + (165447167 / 12500000000000000000) + (96720409 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12638

/-! A coarse bound on the actual paper statistics constant at dimension 12639. -/
namespace BstLean.Part266.Row12639
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12637 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12637 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12637 128 ≤ (12891 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12891 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12639) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12639 : ℕ))
    (by norm_num : (12639 : ℕ) ≤ 16384)
  have ht : paperTail256 12639 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12639 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12639 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12639 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12639 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12639 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12637 128 * √(2 / (12639 : ℝ)) *
      (√(12639 : ℝ) + paperT0 12639 + paperTail256 12639) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12639 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12639 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12639 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12637 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12637 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12639 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12639

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12639
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12639 (61 / 100) 162 (17 / (100 * 12639)) (26 / (10 * 12639)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12639 (61 / 100) 162 (17 / (100 * 12639)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (241741053 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (76506387 / 50000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5317925031 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12639 / 12639 * (61 / 100)) ^ 4 * inverseRadius8 (12639 - 1) /
            envelopeGap 12639 (61 / 100) 162 (17 / (100 * 12639)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12639

namespace BstLean.Part266.Row12639
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12639 162 ≤ (4638201983 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12639 162 ≤ (1547382549 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (371913917 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12639 162 ≤ (1859872267 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12639 162 ≤ (264652701 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12639 162 ≤ (241743629 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (241741053 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (241741053 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (76506387 / 50000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5317925031 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1833741 / 500000000) : ℝ) ≤ √(17 / (100 * 12639) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12639) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1099411327 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19558423633 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12639) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12639) ≤ (111892837 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12639) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12639 * (162 : ℝ) ^ 2 + 26 / (10 * 12639) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12639) : ℝ)) (tA 12639 * 162 ^ 2 + 26 / (10 * 12639)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1833741 / 500000000))) * ((241741053 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1833741 / 500000000)) ^ 3) * ((76506387 / 50000000000000000000000))) + ((5317925031 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1833741 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12639) : ℝ)) d.D d.V d.P (√(tA 12639) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1833741 / 500000000)) ^ 2 * (((1099411327 / 500000000000000)) * ((19558423633 / 500000000000000000)))) + ((5317925031 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12639) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1833741 / 500000000)) * ((241741053 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12639) : ℝ)) (tA 12639 * 162 ^ 2 + 26 / (10 * 12639)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((241741053 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1833741 / 500000000)) ^ 2) * ((76506387 / 50000000000000000000000)) + ((5317925031 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12639) : ℝ)) (√(26 / (10 * 12639) : ℝ)) d.D d.V d.P (√(tA 12639) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1833741 / 500000000)) * (((1099411327 / 500000000000000)) * ((19558423633 / 500000000000000000))) + ((5317925031 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12639) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((241741053 / 50000000000000000000) : ℝ) + ((5317925031 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12639

namespace BstLean.Part266.Row12639
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12639 162 ∧
    0 ≤ (tableEnvelope C).f1 12639 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12639 162 ∧
    0 ≤ (tableEnvelope C).w1 12639 162 ∧ 0 ≤ (tableEnvelope C).w2 12639 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12639 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12639 162 ∧ 0 ≤ d.f1 12639 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12639 162 ∧ 0 ≤ d.w1 12639 162 ∧ 0 ≤ d.w2 12639 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12639 ≤ 2 * (228 / 100 : ℝ) / 12639 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12639 ≤ 2 * (370 / 100 : ℝ) / 12639 := by
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
    (completeRAData (tableEnvelope C) 12639 162).locationBound 12639 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12639 162).energyBound 12639 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12639 162) (d.f1 12639 162) d.f2 ≤
      32 * (((4638201983 / 1000000000000000000) : ℝ) + (1547382549 / 1000000000000000000) + (371913917 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12639 162) (d.w1 12639 162)
      (d.w2 12639 162) ≤
      32 * (((1859872267 / 100000000000000000000) : ℝ) + (264652701 / 20000000000000000000) + (241743629 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12639 162) (d.f1 12639 162) d.f2 ≤
      ((4638201983 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4638201983 / 1000000000000000000)) * ((1547382549 / 1000000000000000000)) * (126 / 100) +
      2 * (((1547382549 / 1000000000000000000)) ^ 2 + 2 * ((4638201983 / 1000000000000000000)) * ((371913917 / 1000000000000000000))) +
      6 * ((1547382549 / 1000000000000000000)) * ((371913917 / 1000000000000000000)) * (126 / 100) + 8 * ((371913917 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12639 162) (d.f1 12639 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12639 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12639 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12639 162) (d.f1 12639 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12639 162) (d.w1 12639 162) (d.w2 12639 162)
  have hwexpr0 : 0 ≤ d.w0 12639 162 + d.w1 12639 162 * √(π / 2) +
      2 * d.w2 12639 162 + energyR16 12639 *
      radiusPolynomialRoot16 (d.w0 12639 162) (d.w1 12639 162) (d.w2 12639 162) := by
    positivity
  constructor
  · change (12639 : ℝ) ^ 8 * (mA 12639 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12639 162) (d.f1 12639 162) d.f2 + locationR16 12639 *
        radiusPolynomialRoot16 (d.f0 12639 162) (d.f1 12639 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12639 : ℝ) ^ 8 * (mA 12639 : ℝ) ^ 8 *
        ((((4638201983 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4638201983 / 1000000000000000000)) * ((1547382549 / 1000000000000000000)) * (126 / 100) +
          2 * (((1547382549 / 1000000000000000000)) ^ 2 + 2 * ((4638201983 / 1000000000000000000)) * ((371913917 / 1000000000000000000))) +
          6 * ((1547382549 / 1000000000000000000)) * ((371913917 / 1000000000000000000)) * (126 / 100) + 8 * ((371913917 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12639) *
          (32 * (((4638201983 / 1000000000000000000) : ℝ) + (1547382549 / 1000000000000000000) + (371913917 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12639 : ℝ) ^ 16 *
      (d.w0 12639 162 + d.w1 12639 162 * √(π / 2) + 2 * d.w2 12639 162 +
        energyR16 12639 * radiusPolynomialRoot16 (d.w0 12639 162) (d.w1 12639 162)
          (d.w2 12639 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12639 : ℝ) ^ 16 *
        (((1859872267 / 100000000000000000000) : ℝ) + ((264652701 / 20000000000000000000)) * (126 / 100) + 2 * ((241743629 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12639) *
          (32 * (((1859872267 / 100000000000000000000) : ℝ) + (264652701 / 20000000000000000000) + (241743629 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12639

/-! A coarse bound on the actual paper statistics constant at dimension 12640. -/
namespace BstLean.Part266.Row12640
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12638 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12638 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12638 128 ≤ (12892 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12892 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12640) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12640 : ℕ))
    (by norm_num : (12640 : ℕ) ≤ 16384)
  have ht : paperTail256 12640 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12640 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12640 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12640 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12640 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12640 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12638 128 * √(2 / (12640 : ℝ)) *
      (√(12640 : ℝ) + paperT0 12640 + paperTail256 12640) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12640 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12640 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12640 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12638 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12638 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12640 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12640

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12640
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12640 (61 / 100) 162 (17 / (100 * 12640)) (26 / (10 * 12640)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12640 (61 / 100) 162 (17 / (100 * 12640)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (241683679 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1529643561 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2657263753 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12640 / 12640 * (61 / 100)) ^ 4 * inverseRadius8 (12640 - 1) /
            envelopeGap 12640 (61 / 100) 162 (17 / (100 * 12640)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12640

namespace BstLean.Part266.Row12640
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12640 162 ≤ (1159321083 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12640 162 ≤ (1547076433 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (371840349 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12640 162 ≤ (929715397 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12640 162 ≤ (1322949419 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12640 162 ≤ (483372507 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (241683679 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (241683679 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1529643561 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2657263753 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3667337 / 1000000000) : ℝ) ≤ √(17 / (100 * 12640) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12640) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (549640427 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4888832237 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12640) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12640) ≤ (22376797 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12640) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12640 * (162 : ℝ) ^ 2 + 26 / (10 * 12640) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12640) : ℝ)) (tA 12640 * 162 ^ 2 + 26 / (10 * 12640)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3667337 / 1000000000))) * ((241683679 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3667337 / 1000000000)) ^ 3) * ((1529643561 / 1000000000000000000000000))) + ((2657263753 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3667337 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12640) : ℝ)) d.D d.V d.P (√(tA 12640) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3667337 / 1000000000)) ^ 2 * (((549640427 / 250000000000000)) * ((4888832237 / 125000000000000000)))) + ((2657263753 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12640) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3667337 / 1000000000)) * ((241683679 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12640) : ℝ)) (tA 12640 * 162 ^ 2 + 26 / (10 * 12640)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((241683679 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3667337 / 1000000000)) ^ 2) * ((1529643561 / 1000000000000000000000000)) + ((2657263753 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12640) : ℝ)) (√(26 / (10 * 12640) : ℝ)) d.D d.V d.P (√(tA 12640) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3667337 / 1000000000)) * (((549640427 / 250000000000000)) * ((4888832237 / 125000000000000000))) + ((2657263753 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12640) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((241683679 / 50000000000000000000) : ℝ) + ((2657263753 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12640

namespace BstLean.Part266.Row12640
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12640 162 ∧
    0 ≤ (tableEnvelope C).f1 12640 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12640 162 ∧
    0 ≤ (tableEnvelope C).w1 12640 162 ∧ 0 ≤ (tableEnvelope C).w2 12640 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12640 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12640 162 ∧ 0 ≤ d.f1 12640 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12640 162 ∧ 0 ≤ d.w1 12640 162 ∧ 0 ≤ d.w2 12640 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12640 ≤ 2 * (228 / 100 : ℝ) / 12640 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12640 ≤ 2 * (370 / 100 : ℝ) / 12640 := by
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
    (completeRAData (tableEnvelope C) 12640 162).locationBound 12640 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12640 162).energyBound 12640 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12640 162) (d.f1 12640 162) d.f2 ≤
      32 * (((1159321083 / 250000000000000000) : ℝ) + (1547076433 / 1000000000000000000) + (371840349 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12640 162) (d.w1 12640 162)
      (d.w2 12640 162) ≤
      32 * (((929715397 / 50000000000000000000) : ℝ) + (1322949419 / 100000000000000000000) + (483372507 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12640 162) (d.f1 12640 162) d.f2 ≤
      ((1159321083 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1159321083 / 250000000000000000)) * ((1547076433 / 1000000000000000000)) * (126 / 100) +
      2 * (((1547076433 / 1000000000000000000)) ^ 2 + 2 * ((1159321083 / 250000000000000000)) * ((371840349 / 1000000000000000000))) +
      6 * ((1547076433 / 1000000000000000000)) * ((371840349 / 1000000000000000000)) * (126 / 100) + 8 * ((371840349 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12640 162) (d.f1 12640 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12640 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12640 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12640 162) (d.f1 12640 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12640 162) (d.w1 12640 162) (d.w2 12640 162)
  have hwexpr0 : 0 ≤ d.w0 12640 162 + d.w1 12640 162 * √(π / 2) +
      2 * d.w2 12640 162 + energyR16 12640 *
      radiusPolynomialRoot16 (d.w0 12640 162) (d.w1 12640 162) (d.w2 12640 162) := by
    positivity
  constructor
  · change (12640 : ℝ) ^ 8 * (mA 12640 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12640 162) (d.f1 12640 162) d.f2 + locationR16 12640 *
        radiusPolynomialRoot16 (d.f0 12640 162) (d.f1 12640 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12640 : ℝ) ^ 8 * (mA 12640 : ℝ) ^ 8 *
        ((((1159321083 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1159321083 / 250000000000000000)) * ((1547076433 / 1000000000000000000)) * (126 / 100) +
          2 * (((1547076433 / 1000000000000000000)) ^ 2 + 2 * ((1159321083 / 250000000000000000)) * ((371840349 / 1000000000000000000))) +
          6 * ((1547076433 / 1000000000000000000)) * ((371840349 / 1000000000000000000)) * (126 / 100) + 8 * ((371840349 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12640) *
          (32 * (((1159321083 / 250000000000000000) : ℝ) + (1547076433 / 1000000000000000000) + (371840349 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12640 : ℝ) ^ 16 *
      (d.w0 12640 162 + d.w1 12640 162 * √(π / 2) + 2 * d.w2 12640 162 +
        energyR16 12640 * radiusPolynomialRoot16 (d.w0 12640 162) (d.w1 12640 162)
          (d.w2 12640 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12640 : ℝ) ^ 16 *
        (((929715397 / 50000000000000000000) : ℝ) + ((1322949419 / 100000000000000000000)) * (126 / 100) + 2 * ((483372507 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12640) *
          (32 * (((929715397 / 50000000000000000000) : ℝ) + (1322949419 / 100000000000000000000) + (483372507 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12640

/-! A coarse bound on the actual paper statistics constant at dimension 12641. -/
namespace BstLean.Part266.Row12641
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12639 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12639 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12639 128 ≤ (12893 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12893 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12641) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12641 : ℕ))
    (by norm_num : (12641 : ℕ) ≤ 16384)
  have ht : paperTail256 12641 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12641 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12641 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12641 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12641 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12641 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12639 128 * √(2 / (12641 : ℝ)) *
      (√(12641 : ℝ) + paperT0 12641 + paperTail256 12641) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12641 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12641 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12641 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12639 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12639 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12641 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12641

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12641
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12641 (61 / 100) 162 (17 / (100 * 12641)) (26 / (10 * 12641)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12641 (61 / 100) 162 (17 / (100 * 12641)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (483252647 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1529159573 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (212445297 / 40000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12641 / 12641 * (61 / 100)) ^ 4 * inverseRadius8 (12641 - 1) /
            envelopeGap 12641 (61 / 100) 162 (17 / (100 * 12641)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12641

namespace BstLean.Part266.Row12641
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12641 162 ≤ (1159091749 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12641 162 ≤ (1546770417 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (74353361 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12641 162 ≤ (74359579 / 4000000000000000000)
  w1 : (tableEnvelope C).w1 12641 162 ≤ (1322635439 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12641 162 ≤ (7550903 / 1562500000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (483252647 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (483252647 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1529159573 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (212445297 / 40000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((458399 / 125000000) : ℝ) ≤ √(17 / (100 * 12641) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12641) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (439660163 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9776117497 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12641) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12641) ≤ (55937567 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12641) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12641 * (162 : ℝ) ^ 2 + 26 / (10 * 12641) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12641) : ℝ)) (tA 12641 * 162 ^ 2 + 26 / (10 * 12641)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((458399 / 125000000))) * ((483252647 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((458399 / 125000000)) ^ 3) * ((1529159573 / 1000000000000000000000000))) + ((212445297 / 40000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((458399 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12641) : ℝ)) d.D d.V d.P (√(tA 12641) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((458399 / 125000000)) ^ 2 * (((439660163 / 200000000000000)) * ((9776117497 / 250000000000000000)))) + ((212445297 / 40000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12641) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((458399 / 125000000)) * ((483252647 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12641) : ℝ)) (tA 12641 * 162 ^ 2 + 26 / (10 * 12641)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((483252647 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((458399 / 125000000)) ^ 2) * ((1529159573 / 1000000000000000000000000)) + ((212445297 / 40000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12641) : ℝ)) (√(26 / (10 * 12641) : ℝ)) d.D d.V d.P (√(tA 12641) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((458399 / 125000000)) * (((439660163 / 200000000000000)) * ((9776117497 / 250000000000000000))) + ((212445297 / 40000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12641) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((483252647 / 100000000000000000000) : ℝ) + ((212445297 / 40000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12641

namespace BstLean.Part266.Row12641
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12641 162 ∧
    0 ≤ (tableEnvelope C).f1 12641 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12641 162 ∧
    0 ≤ (tableEnvelope C).w1 12641 162 ∧ 0 ≤ (tableEnvelope C).w2 12641 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12641 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12641 162 ∧ 0 ≤ d.f1 12641 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12641 162 ∧ 0 ≤ d.w1 12641 162 ∧ 0 ≤ d.w2 12641 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12641 ≤ 2 * (228 / 100 : ℝ) / 12641 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12641 ≤ 2 * (370 / 100 : ℝ) / 12641 := by
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
    (completeRAData (tableEnvelope C) 12641 162).locationBound 12641 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12641 162).energyBound 12641 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12641 162) (d.f1 12641 162) d.f2 ≤
      32 * (((1159091749 / 250000000000000000) : ℝ) + (1546770417 / 1000000000000000000) + (74353361 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12641 162) (d.w1 12641 162)
      (d.w2 12641 162) ≤
      32 * (((74359579 / 4000000000000000000) : ℝ) + (1322635439 / 100000000000000000000) + (7550903 / 1562500000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12641 162) (d.f1 12641 162) d.f2 ≤
      ((1159091749 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1159091749 / 250000000000000000)) * ((1546770417 / 1000000000000000000)) * (126 / 100) +
      2 * (((1546770417 / 1000000000000000000)) ^ 2 + 2 * ((1159091749 / 250000000000000000)) * ((74353361 / 200000000000000000))) +
      6 * ((1546770417 / 1000000000000000000)) * ((74353361 / 200000000000000000)) * (126 / 100) + 8 * ((74353361 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12641 162) (d.f1 12641 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12641 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12641 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12641 162) (d.f1 12641 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12641 162) (d.w1 12641 162) (d.w2 12641 162)
  have hwexpr0 : 0 ≤ d.w0 12641 162 + d.w1 12641 162 * √(π / 2) +
      2 * d.w2 12641 162 + energyR16 12641 *
      radiusPolynomialRoot16 (d.w0 12641 162) (d.w1 12641 162) (d.w2 12641 162) := by
    positivity
  constructor
  · change (12641 : ℝ) ^ 8 * (mA 12641 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12641 162) (d.f1 12641 162) d.f2 + locationR16 12641 *
        radiusPolynomialRoot16 (d.f0 12641 162) (d.f1 12641 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12641 : ℝ) ^ 8 * (mA 12641 : ℝ) ^ 8 *
        ((((1159091749 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1159091749 / 250000000000000000)) * ((1546770417 / 1000000000000000000)) * (126 / 100) +
          2 * (((1546770417 / 1000000000000000000)) ^ 2 + 2 * ((1159091749 / 250000000000000000)) * ((74353361 / 200000000000000000))) +
          6 * ((1546770417 / 1000000000000000000)) * ((74353361 / 200000000000000000)) * (126 / 100) + 8 * ((74353361 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12641) *
          (32 * (((1159091749 / 250000000000000000) : ℝ) + (1546770417 / 1000000000000000000) + (74353361 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12641 : ℝ) ^ 16 *
      (d.w0 12641 162 + d.w1 12641 162 * √(π / 2) + 2 * d.w2 12641 162 +
        energyR16 12641 * radiusPolynomialRoot16 (d.w0 12641 162) (d.w1 12641 162)
          (d.w2 12641 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12641 : ℝ) ^ 16 *
        (((74359579 / 4000000000000000000) : ℝ) + ((1322635439 / 100000000000000000000)) * (126 / 100) + 2 * ((7550903 / 1562500000000000000)) +
          (2 * (370 / 100 : ℝ) / 12641) *
          (32 * (((74359579 / 4000000000000000000) : ℝ) + (1322635439 / 100000000000000000000) + (7550903 / 1562500000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12641

/-! A coarse bound on the actual paper statistics constant at dimension 12642. -/
namespace BstLean.Part266.Row12642
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12640 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12640 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12640 128 ≤ (12894 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12894 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12642) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12642 : ℕ))
    (by norm_num : (12642 : ℕ) ≤ 16384)
  have ht : paperTail256 12642 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12642 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12642 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12642 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12642 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12642 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12640 128 * √(2 / (12642 : ℝ)) *
      (√(12642 : ℝ) + paperT0 12642 + paperTail256 12642) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12642 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12642 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12642 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12640 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12640 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12642 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12642

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12642
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12642 (61 / 100) 162 (17 / (100 * 12642)) (26 / (10 * 12642)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12642 (61 / 100) 162 (17 / (100 * 12642)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (120784493 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1528675777 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5307739787 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12642 / 12642 * (61 / 100)) ^ 4 * inverseRadius8 (12642 - 1) /
            envelopeGap 12642 (61 / 100) 162 (17 / (100 * 12642)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12642

namespace BstLean.Part266.Row12642
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12642 162 ≤ (4635449979 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12642 162 ≤ (3092929 / 2000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (185846641 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12642 162 ≤ (464637077 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12642 162 ≤ (264464313 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12642 162 ≤ (241571557 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (120784493 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (120784493 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1528675777 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5307739787 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3667047 / 1000000000) : ℝ) ≤ √(17 / (100 * 12642) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12642) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2198039973 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9774570889 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12642) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12642) ≤ (22373257 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12642) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12642 * (162 : ℝ) ^ 2 + 26 / (10 * 12642) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12642) : ℝ)) (tA 12642 * 162 ^ 2 + 26 / (10 * 12642)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3667047 / 1000000000))) * ((120784493 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3667047 / 1000000000)) ^ 3) * ((1528675777 / 1000000000000000000000000))) + ((5307739787 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3667047 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12642) : ℝ)) d.D d.V d.P (√(tA 12642) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3667047 / 1000000000)) ^ 2 * (((2198039973 / 1000000000000000)) * ((9774570889 / 250000000000000000)))) + ((5307739787 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12642) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3667047 / 1000000000)) * ((120784493 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12642) : ℝ)) (tA 12642 * 162 ^ 2 + 26 / (10 * 12642)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((120784493 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3667047 / 1000000000)) ^ 2) * ((1528675777 / 1000000000000000000000000)) + ((5307739787 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12642) : ℝ)) (√(26 / (10 * 12642) : ℝ)) d.D d.V d.P (√(tA 12642) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3667047 / 1000000000)) * (((2198039973 / 1000000000000000)) * ((9774570889 / 250000000000000000))) + ((5307739787 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12642) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((120784493 / 25000000000000000000) : ℝ) + ((5307739787 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12642

namespace BstLean.Part266.Row12642
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12642 162 ∧
    0 ≤ (tableEnvelope C).f1 12642 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12642 162 ∧
    0 ≤ (tableEnvelope C).w1 12642 162 ∧ 0 ≤ (tableEnvelope C).w2 12642 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12642 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12642 162 ∧ 0 ≤ d.f1 12642 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12642 162 ∧ 0 ≤ d.w1 12642 162 ∧ 0 ≤ d.w2 12642 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12642 ≤ 2 * (228 / 100 : ℝ) / 12642 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12642 ≤ 2 * (370 / 100 : ℝ) / 12642 := by
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
    (completeRAData (tableEnvelope C) 12642 162).locationBound 12642 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12642 162).energyBound 12642 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12642 162) (d.f1 12642 162) d.f2 ≤
      32 * (((4635449979 / 1000000000000000000) : ℝ) + (3092929 / 2000000000000000) + (185846641 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12642 162) (d.w1 12642 162)
      (d.w2 12642 162) ≤
      32 * (((464637077 / 25000000000000000000) : ℝ) + (264464313 / 20000000000000000000) + (241571557 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12642 162) (d.f1 12642 162) d.f2 ≤
      ((4635449979 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4635449979 / 1000000000000000000)) * ((3092929 / 2000000000000000)) * (126 / 100) +
      2 * (((3092929 / 2000000000000000)) ^ 2 + 2 * ((4635449979 / 1000000000000000000)) * ((185846641 / 500000000000000000))) +
      6 * ((3092929 / 2000000000000000)) * ((185846641 / 500000000000000000)) * (126 / 100) + 8 * ((185846641 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12642 162) (d.f1 12642 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12642 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12642 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12642 162) (d.f1 12642 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12642 162) (d.w1 12642 162) (d.w2 12642 162)
  have hwexpr0 : 0 ≤ d.w0 12642 162 + d.w1 12642 162 * √(π / 2) +
      2 * d.w2 12642 162 + energyR16 12642 *
      radiusPolynomialRoot16 (d.w0 12642 162) (d.w1 12642 162) (d.w2 12642 162) := by
    positivity
  constructor
  · change (12642 : ℝ) ^ 8 * (mA 12642 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12642 162) (d.f1 12642 162) d.f2 + locationR16 12642 *
        radiusPolynomialRoot16 (d.f0 12642 162) (d.f1 12642 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12642 : ℝ) ^ 8 * (mA 12642 : ℝ) ^ 8 *
        ((((4635449979 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4635449979 / 1000000000000000000)) * ((3092929 / 2000000000000000)) * (126 / 100) +
          2 * (((3092929 / 2000000000000000)) ^ 2 + 2 * ((4635449979 / 1000000000000000000)) * ((185846641 / 500000000000000000))) +
          6 * ((3092929 / 2000000000000000)) * ((185846641 / 500000000000000000)) * (126 / 100) + 8 * ((185846641 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12642) *
          (32 * (((4635449979 / 1000000000000000000) : ℝ) + (3092929 / 2000000000000000) + (185846641 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12642 : ℝ) ^ 16 *
      (d.w0 12642 162 + d.w1 12642 162 * √(π / 2) + 2 * d.w2 12642 162 +
        energyR16 12642 * radiusPolynomialRoot16 (d.w0 12642 162) (d.w1 12642 162)
          (d.w2 12642 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12642 : ℝ) ^ 16 *
        (((464637077 / 25000000000000000000) : ℝ) + ((264464313 / 20000000000000000000)) * (126 / 100) + 2 * ((241571557 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12642) *
          (32 * (((464637077 / 25000000000000000000) : ℝ) + (264464313 / 20000000000000000000) + (241571557 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12642

/-! A coarse bound on the actual paper statistics constant at dimension 12643. -/
namespace BstLean.Part266.Row12643
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12641 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12641 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12641 128 ≤ (12895 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12895 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12643) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12643 : ℕ))
    (by norm_num : (12643 : ℕ) ≤ 16384)
  have ht : paperTail256 12643 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12643 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12643 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12643 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12643 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12643 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12641 128 * √(2 / (12643 : ℝ)) *
      (√(12643 : ℝ) + paperT0 12643 + paperTail256 12643) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12643 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12643 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12643 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12641 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12641 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12643 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12643

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12643
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12643 (61 / 100) 162 (17 / (100 * 12643)) (26 / (10 * 12643)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12643 (61 / 100) 162 (17 / (100 * 12643)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (241511667 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (382048043 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5304349589 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12643 / 12643 * (61 / 100)) ^ 4 * inverseRadius8 (12643 - 1) /
            envelopeGap 12643 (61 / 100) 162 (17 / (100 * 12643)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12643

namespace BstLean.Part266.Row12643
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12643 162 ≤ (2317266639 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12643 162 ≤ (1546158683 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (371619781 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12643 162 ≤ (929053647 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12643 162 ≤ (330501949 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12643 162 ≤ (483028473 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (241511667 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (241511667 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (382048043 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5304349589 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1833451 / 500000000) : ℝ) ≤ √(17 / (100 * 12643) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12643) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (137361199 / 62500000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9773024647 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12643) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12643) ≤ (27964359 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12643) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12643 * (162 : ℝ) ^ 2 + 26 / (10 * 12643) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12643) : ℝ)) (tA 12643 * 162 ^ 2 + 26 / (10 * 12643)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1833451 / 500000000))) * ((241511667 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1833451 / 500000000)) ^ 3) * ((382048043 / 250000000000000000000000))) + ((5304349589 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1833451 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12643) : ℝ)) d.D d.V d.P (√(tA 12643) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1833451 / 500000000)) ^ 2 * (((137361199 / 62500000000000)) * ((9773024647 / 250000000000000000)))) + ((5304349589 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12643) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1833451 / 500000000)) * ((241511667 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12643) : ℝ)) (tA 12643 * 162 ^ 2 + 26 / (10 * 12643)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((241511667 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1833451 / 500000000)) ^ 2) * ((382048043 / 250000000000000000000000)) + ((5304349589 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12643) : ℝ)) (√(26 / (10 * 12643) : ℝ)) d.D d.V d.P (√(tA 12643) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1833451 / 500000000)) * (((137361199 / 62500000000000)) * ((9773024647 / 250000000000000000))) + ((5304349589 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12643) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((241511667 / 50000000000000000000) : ℝ) + ((5304349589 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12643

namespace BstLean.Part266.Row12643
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12643 162 ∧
    0 ≤ (tableEnvelope C).f1 12643 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12643 162 ∧
    0 ≤ (tableEnvelope C).w1 12643 162 ∧ 0 ≤ (tableEnvelope C).w2 12643 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12643 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12643 162 ∧ 0 ≤ d.f1 12643 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12643 162 ∧ 0 ≤ d.w1 12643 162 ∧ 0 ≤ d.w2 12643 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12643 ≤ 2 * (228 / 100 : ℝ) / 12643 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12643 ≤ 2 * (370 / 100 : ℝ) / 12643 := by
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
    (completeRAData (tableEnvelope C) 12643 162).locationBound 12643 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12643 162).energyBound 12643 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12643 162) (d.f1 12643 162) d.f2 ≤
      32 * (((2317266639 / 500000000000000000) : ℝ) + (1546158683 / 1000000000000000000) + (371619781 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12643 162) (d.w1 12643 162)
      (d.w2 12643 162) ≤
      32 * (((929053647 / 50000000000000000000) : ℝ) + (330501949 / 25000000000000000000) + (483028473 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12643 162) (d.f1 12643 162) d.f2 ≤
      ((2317266639 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2317266639 / 500000000000000000)) * ((1546158683 / 1000000000000000000)) * (126 / 100) +
      2 * (((1546158683 / 1000000000000000000)) ^ 2 + 2 * ((2317266639 / 500000000000000000)) * ((371619781 / 1000000000000000000))) +
      6 * ((1546158683 / 1000000000000000000)) * ((371619781 / 1000000000000000000)) * (126 / 100) + 8 * ((371619781 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12643 162) (d.f1 12643 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12643 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12643 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12643 162) (d.f1 12643 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12643 162) (d.w1 12643 162) (d.w2 12643 162)
  have hwexpr0 : 0 ≤ d.w0 12643 162 + d.w1 12643 162 * √(π / 2) +
      2 * d.w2 12643 162 + energyR16 12643 *
      radiusPolynomialRoot16 (d.w0 12643 162) (d.w1 12643 162) (d.w2 12643 162) := by
    positivity
  constructor
  · change (12643 : ℝ) ^ 8 * (mA 12643 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12643 162) (d.f1 12643 162) d.f2 + locationR16 12643 *
        radiusPolynomialRoot16 (d.f0 12643 162) (d.f1 12643 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12643 : ℝ) ^ 8 * (mA 12643 : ℝ) ^ 8 *
        ((((2317266639 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2317266639 / 500000000000000000)) * ((1546158683 / 1000000000000000000)) * (126 / 100) +
          2 * (((1546158683 / 1000000000000000000)) ^ 2 + 2 * ((2317266639 / 500000000000000000)) * ((371619781 / 1000000000000000000))) +
          6 * ((1546158683 / 1000000000000000000)) * ((371619781 / 1000000000000000000)) * (126 / 100) + 8 * ((371619781 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12643) *
          (32 * (((2317266639 / 500000000000000000) : ℝ) + (1546158683 / 1000000000000000000) + (371619781 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12643 : ℝ) ^ 16 *
      (d.w0 12643 162 + d.w1 12643 162 * √(π / 2) + 2 * d.w2 12643 162 +
        energyR16 12643 * radiusPolynomialRoot16 (d.w0 12643 162) (d.w1 12643 162)
          (d.w2 12643 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12643 : ℝ) ^ 16 *
        (((929053647 / 50000000000000000000) : ℝ) + ((330501949 / 25000000000000000000)) * (126 / 100) + 2 * ((483028473 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12643) *
          (32 * (((929053647 / 50000000000000000000) : ℝ) + (330501949 / 25000000000000000000) + (483028473 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12643

/-! A coarse bound on the actual paper statistics constant at dimension 12644. -/
namespace BstLean.Part266.Row12644
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12642 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12642 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12642 128 ≤ (12896 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12896 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12644) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12644 : ℕ))
    (by norm_num : (12644 : ℕ) ≤ 16384)
  have ht : paperTail256 12644 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12644 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12644 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12644 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12644 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12644 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12642 128 * √(2 / (12644 : ℝ)) *
      (√(12644 : ℝ) + paperT0 12644 + paperTail256 12644) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12644 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12644 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12644 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12642 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12642 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12644 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12644

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12644
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12644 (61 / 100) 162 (17 / (100 * 12644)) (26 / (10 * 12644)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12644 (61 / 100) 162 (17 / (100 * 12644)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (482908731 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (763854379 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5300961829 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12644 / 12644 * (61 / 100)) ^ 4 * inverseRadius8 (12644 - 1) /
            envelopeGap 12644 (61 / 100) 162 (17 / (100 * 12644)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12644

namespace BstLean.Part266.Row12644
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12644 162 ≤ (4633616893 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12644 162 ≤ (1545852963 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (185773151 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12644 162 ≤ (1857666431 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12644 162 ≤ (330423533 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12644 162 ≤ (241456933 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (482908731 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (482908731 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (763854379 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5300961829 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3666757 / 1000000000) : ℝ) ≤ √(17 / (100 * 12644) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12644) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (549379611 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7817183017 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12644) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12644) ≤ (11184859 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12644) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12644 * (162 : ℝ) ^ 2 + 26 / (10 * 12644) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12644) : ℝ)) (tA 12644 * 162 ^ 2 + 26 / (10 * 12644)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3666757 / 1000000000))) * ((482908731 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3666757 / 1000000000)) ^ 3) * ((763854379 / 500000000000000000000000))) + ((5300961829 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3666757 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12644) : ℝ)) d.D d.V d.P (√(tA 12644) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3666757 / 1000000000)) ^ 2 * (((549379611 / 250000000000000)) * ((7817183017 / 200000000000000000)))) + ((5300961829 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12644) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3666757 / 1000000000)) * ((482908731 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12644) : ℝ)) (tA 12644 * 162 ^ 2 + 26 / (10 * 12644)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((482908731 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3666757 / 1000000000)) ^ 2) * ((763854379 / 500000000000000000000000)) + ((5300961829 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12644) : ℝ)) (√(26 / (10 * 12644) : ℝ)) d.D d.V d.P (√(tA 12644) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3666757 / 1000000000)) * (((549379611 / 250000000000000)) * ((7817183017 / 200000000000000000))) + ((5300961829 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12644) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((482908731 / 100000000000000000000) : ℝ) + ((5300961829 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12644

namespace BstLean.Part266.Row12644
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12644 162 ∧
    0 ≤ (tableEnvelope C).f1 12644 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12644 162 ∧
    0 ≤ (tableEnvelope C).w1 12644 162 ∧ 0 ≤ (tableEnvelope C).w2 12644 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12644 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12644 162 ∧ 0 ≤ d.f1 12644 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12644 162 ∧ 0 ≤ d.w1 12644 162 ∧ 0 ≤ d.w2 12644 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12644 ≤ 2 * (228 / 100 : ℝ) / 12644 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12644 ≤ 2 * (370 / 100 : ℝ) / 12644 := by
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
    (completeRAData (tableEnvelope C) 12644 162).locationBound 12644 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12644 162).energyBound 12644 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12644 162) (d.f1 12644 162) d.f2 ≤
      32 * (((4633616893 / 1000000000000000000) : ℝ) + (1545852963 / 1000000000000000000) + (185773151 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12644 162) (d.w1 12644 162)
      (d.w2 12644 162) ≤
      32 * (((1857666431 / 100000000000000000000) : ℝ) + (330423533 / 25000000000000000000) + (241456933 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12644 162) (d.f1 12644 162) d.f2 ≤
      ((4633616893 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4633616893 / 1000000000000000000)) * ((1545852963 / 1000000000000000000)) * (126 / 100) +
      2 * (((1545852963 / 1000000000000000000)) ^ 2 + 2 * ((4633616893 / 1000000000000000000)) * ((185773151 / 500000000000000000))) +
      6 * ((1545852963 / 1000000000000000000)) * ((185773151 / 500000000000000000)) * (126 / 100) + 8 * ((185773151 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12644 162) (d.f1 12644 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12644 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12644 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12644 162) (d.f1 12644 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12644 162) (d.w1 12644 162) (d.w2 12644 162)
  have hwexpr0 : 0 ≤ d.w0 12644 162 + d.w1 12644 162 * √(π / 2) +
      2 * d.w2 12644 162 + energyR16 12644 *
      radiusPolynomialRoot16 (d.w0 12644 162) (d.w1 12644 162) (d.w2 12644 162) := by
    positivity
  constructor
  · change (12644 : ℝ) ^ 8 * (mA 12644 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12644 162) (d.f1 12644 162) d.f2 + locationR16 12644 *
        radiusPolynomialRoot16 (d.f0 12644 162) (d.f1 12644 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12644 : ℝ) ^ 8 * (mA 12644 : ℝ) ^ 8 *
        ((((4633616893 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4633616893 / 1000000000000000000)) * ((1545852963 / 1000000000000000000)) * (126 / 100) +
          2 * (((1545852963 / 1000000000000000000)) ^ 2 + 2 * ((4633616893 / 1000000000000000000)) * ((185773151 / 500000000000000000))) +
          6 * ((1545852963 / 1000000000000000000)) * ((185773151 / 500000000000000000)) * (126 / 100) + 8 * ((185773151 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12644) *
          (32 * (((4633616893 / 1000000000000000000) : ℝ) + (1545852963 / 1000000000000000000) + (185773151 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12644 : ℝ) ^ 16 *
      (d.w0 12644 162 + d.w1 12644 162 * √(π / 2) + 2 * d.w2 12644 162 +
        energyR16 12644 * radiusPolynomialRoot16 (d.w0 12644 162) (d.w1 12644 162)
          (d.w2 12644 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12644 : ℝ) ^ 16 *
        (((1857666431 / 100000000000000000000) : ℝ) + ((330423533 / 25000000000000000000)) * (126 / 100) + 2 * ((241456933 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12644) *
          (32 * (((1857666431 / 100000000000000000000) : ℝ) + (330423533 / 25000000000000000000) + (241456933 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12644

/-! A coarse bound on the actual paper statistics constant at dimension 12645. -/
namespace BstLean.Part266.Row12645
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12643 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12643 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12643 128 ≤ (12897 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12897 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12645) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12645 : ℕ))
    (by norm_num : (12645 : ℕ) ≤ 16384)
  have ht : paperTail256 12645 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12645 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12645 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12645 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12645 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12645 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12643 128 * √(2 / (12645 : ℝ)) *
      (√(12645 : ℝ) + paperT0 12645 + paperTail256 12645) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12645 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12645 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12645 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12643 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12643 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12645 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12645

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12645
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12645 (61 / 100) 162 (17 / (100 * 12645)) (26 / (10 * 12645)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12645 (61 / 100) 162 (17 / (100 * 12645)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (96558833 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (305445107 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2648788253 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12645 / 12645 * (61 / 100)) ^ 4 * inverseRadius8 (12645 - 1) /
            envelopeGap 12645 (61 / 100) 162 (17 / (100 * 12645)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12645

namespace BstLean.Part266.Row12645
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12645 162 ≤ (4632700823 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12645 162 ≤ (96596709 / 62500000000000000)
  f2 : (tableEnvelope C).f2 ≤ (185736423 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12645 162 ≤ (1857225721 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12645 162 ≤ (660690287 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12645 162 ≤ (482799297 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (96558833 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (96558833 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (305445107 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2648788253 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((916653 / 250000000) : ℝ) ≤ √(17 / (100 * 12645) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12645) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2197257757 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39079733047 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12645) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12645) ≤ (218437 / 1953125000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12645) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12645 * (162 : ℝ) ^ 2 + 26 / (10 * 12645) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12645) : ℝ)) (tA 12645 * 162 ^ 2 + 26 / (10 * 12645)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((916653 / 250000000))) * ((96558833 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((916653 / 250000000)) ^ 3) * ((305445107 / 200000000000000000000000))) + ((2648788253 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((916653 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12645) : ℝ)) d.D d.V d.P (√(tA 12645) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((916653 / 250000000)) ^ 2 * (((2197257757 / 1000000000000000)) * ((39079733047 / 1000000000000000000)))) + ((2648788253 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12645) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((916653 / 250000000)) * ((96558833 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12645) : ℝ)) (tA 12645 * 162 ^ 2 + 26 / (10 * 12645)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((96558833 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((916653 / 250000000)) ^ 2) * ((305445107 / 200000000000000000000000)) + ((2648788253 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12645) : ℝ)) (√(26 / (10 * 12645) : ℝ)) d.D d.V d.P (√(tA 12645) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((916653 / 250000000)) * (((2197257757 / 1000000000000000)) * ((39079733047 / 1000000000000000000))) + ((2648788253 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12645) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((96558833 / 20000000000000000000) : ℝ) + ((2648788253 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12645

namespace BstLean.Part266.Row12645
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12645 162 ∧
    0 ≤ (tableEnvelope C).f1 12645 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12645 162 ∧
    0 ≤ (tableEnvelope C).w1 12645 162 ∧ 0 ≤ (tableEnvelope C).w2 12645 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12645 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12645 162 ∧ 0 ≤ d.f1 12645 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12645 162 ∧ 0 ≤ d.w1 12645 162 ∧ 0 ≤ d.w2 12645 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12645 ≤ 2 * (228 / 100 : ℝ) / 12645 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12645 ≤ 2 * (370 / 100 : ℝ) / 12645 := by
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
    (completeRAData (tableEnvelope C) 12645 162).locationBound 12645 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12645 162).energyBound 12645 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12645 162) (d.f1 12645 162) d.f2 ≤
      32 * (((4632700823 / 1000000000000000000) : ℝ) + (96596709 / 62500000000000000) + (185736423 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12645 162) (d.w1 12645 162)
      (d.w2 12645 162) ≤
      32 * (((1857225721 / 100000000000000000000) : ℝ) + (660690287 / 50000000000000000000) + (482799297 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12645 162) (d.f1 12645 162) d.f2 ≤
      ((4632700823 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4632700823 / 1000000000000000000)) * ((96596709 / 62500000000000000)) * (126 / 100) +
      2 * (((96596709 / 62500000000000000)) ^ 2 + 2 * ((4632700823 / 1000000000000000000)) * ((185736423 / 500000000000000000))) +
      6 * ((96596709 / 62500000000000000)) * ((185736423 / 500000000000000000)) * (126 / 100) + 8 * ((185736423 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12645 162) (d.f1 12645 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12645 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12645 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12645 162) (d.f1 12645 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12645 162) (d.w1 12645 162) (d.w2 12645 162)
  have hwexpr0 : 0 ≤ d.w0 12645 162 + d.w1 12645 162 * √(π / 2) +
      2 * d.w2 12645 162 + energyR16 12645 *
      radiusPolynomialRoot16 (d.w0 12645 162) (d.w1 12645 162) (d.w2 12645 162) := by
    positivity
  constructor
  · change (12645 : ℝ) ^ 8 * (mA 12645 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12645 162) (d.f1 12645 162) d.f2 + locationR16 12645 *
        radiusPolynomialRoot16 (d.f0 12645 162) (d.f1 12645 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12645 : ℝ) ^ 8 * (mA 12645 : ℝ) ^ 8 *
        ((((4632700823 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4632700823 / 1000000000000000000)) * ((96596709 / 62500000000000000)) * (126 / 100) +
          2 * (((96596709 / 62500000000000000)) ^ 2 + 2 * ((4632700823 / 1000000000000000000)) * ((185736423 / 500000000000000000))) +
          6 * ((96596709 / 62500000000000000)) * ((185736423 / 500000000000000000)) * (126 / 100) + 8 * ((185736423 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12645) *
          (32 * (((4632700823 / 1000000000000000000) : ℝ) + (96596709 / 62500000000000000) + (185736423 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12645 : ℝ) ^ 16 *
      (d.w0 12645 162 + d.w1 12645 162 * √(π / 2) + 2 * d.w2 12645 162 +
        energyR16 12645 * radiusPolynomialRoot16 (d.w0 12645 162) (d.w1 12645 162)
          (d.w2 12645 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12645 : ℝ) ^ 16 *
        (((1857225721 / 100000000000000000000) : ℝ) + ((660690287 / 50000000000000000000)) * (126 / 100) + 2 * ((482799297 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12645) *
          (32 * (((1857225721 / 100000000000000000000) : ℝ) + (660690287 / 50000000000000000000) + (482799297 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12645

/-! A coarse bound on the actual paper statistics constant at dimension 12646. -/
namespace BstLean.Part266.Row12646
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12644 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12644 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12644 128 ≤ (12898 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12898 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12646) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12646 : ℕ))
    (by norm_num : (12646 : ℕ) ≤ 16384)
  have ht : paperTail256 12646 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12646 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12646 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12646 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12646 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12646 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12644 128 * √(2 / (12646 : ℝ)) *
      (√(12646 : ℝ) + paperT0 12646 + paperTail256 12646) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12646 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12646 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12646 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12644 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12644 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12646 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12646

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12646
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12646 (61 / 100) 162 (17 / (100 * 12646)) (26 / (10 * 12646)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12646 (61 / 100) 162 (17 / (100 * 12646)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (96535927 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1526742503 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5294193617 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12646 / 12646 * (61 / 100)) ^ 4 * inverseRadius8 (12646 - 1) /
            envelopeGap 12646 (61 / 100) 162 (17 / (100 * 12646)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12646

namespace BstLean.Part266.Row12646
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12646 162 ≤ (463178507 / 100000000000000000)
  f1 : (tableEnvelope C).f1 12646 162 ≤ (1545241823 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (371399411 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12646 162 ≤ (1856785163 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12646 162 ≤ (1321067121 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12646 162 ≤ (120671191 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (96535927 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (96535927 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1526742503 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5294193617 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3666467 / 1000000000) : ℝ) ≤ √(17 / (100 * 12646) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12646) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1098498561 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1562942099 / 40000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12646) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12646) ≤ (111830901 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12646) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12646 * (162 : ℝ) ^ 2 + 26 / (10 * 12646) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12646) : ℝ)) (tA 12646 * 162 ^ 2 + 26 / (10 * 12646)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3666467 / 1000000000))) * ((96535927 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3666467 / 1000000000)) ^ 3) * ((1526742503 / 1000000000000000000000000))) + ((5294193617 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3666467 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12646) : ℝ)) d.D d.V d.P (√(tA 12646) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3666467 / 1000000000)) ^ 2 * (((1098498561 / 500000000000000)) * ((1562942099 / 40000000000000000)))) + ((5294193617 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12646) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3666467 / 1000000000)) * ((96535927 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12646) : ℝ)) (tA 12646 * 162 ^ 2 + 26 / (10 * 12646)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((96535927 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3666467 / 1000000000)) ^ 2) * ((1526742503 / 1000000000000000000000000)) + ((5294193617 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12646) : ℝ)) (√(26 / (10 * 12646) : ℝ)) d.D d.V d.P (√(tA 12646) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3666467 / 1000000000)) * (((1098498561 / 500000000000000)) * ((1562942099 / 40000000000000000))) + ((5294193617 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12646) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((96535927 / 20000000000000000000) : ℝ) + ((5294193617 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12646

namespace BstLean.Part266.Row12646
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12646 162 ∧
    0 ≤ (tableEnvelope C).f1 12646 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12646 162 ∧
    0 ≤ (tableEnvelope C).w1 12646 162 ∧ 0 ≤ (tableEnvelope C).w2 12646 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12646 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12646 162 ∧ 0 ≤ d.f1 12646 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12646 162 ∧ 0 ≤ d.w1 12646 162 ∧ 0 ≤ d.w2 12646 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12646 ≤ 2 * (228 / 100 : ℝ) / 12646 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12646 ≤ 2 * (370 / 100 : ℝ) / 12646 := by
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
    (completeRAData (tableEnvelope C) 12646 162).locationBound 12646 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12646 162).energyBound 12646 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12646 162) (d.f1 12646 162) d.f2 ≤
      32 * (((463178507 / 100000000000000000) : ℝ) + (1545241823 / 1000000000000000000) + (371399411 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12646 162) (d.w1 12646 162)
      (d.w2 12646 162) ≤
      32 * (((1856785163 / 100000000000000000000) : ℝ) + (1321067121 / 100000000000000000000) + (120671191 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12646 162) (d.f1 12646 162) d.f2 ≤
      ((463178507 / 100000000000000000) : ℝ) ^ 2 + 2 * ((463178507 / 100000000000000000)) * ((1545241823 / 1000000000000000000)) * (126 / 100) +
      2 * (((1545241823 / 1000000000000000000)) ^ 2 + 2 * ((463178507 / 100000000000000000)) * ((371399411 / 1000000000000000000))) +
      6 * ((1545241823 / 1000000000000000000)) * ((371399411 / 1000000000000000000)) * (126 / 100) + 8 * ((371399411 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12646 162) (d.f1 12646 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12646 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12646 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12646 162) (d.f1 12646 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12646 162) (d.w1 12646 162) (d.w2 12646 162)
  have hwexpr0 : 0 ≤ d.w0 12646 162 + d.w1 12646 162 * √(π / 2) +
      2 * d.w2 12646 162 + energyR16 12646 *
      radiusPolynomialRoot16 (d.w0 12646 162) (d.w1 12646 162) (d.w2 12646 162) := by
    positivity
  constructor
  · change (12646 : ℝ) ^ 8 * (mA 12646 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12646 162) (d.f1 12646 162) d.f2 + locationR16 12646 *
        radiusPolynomialRoot16 (d.f0 12646 162) (d.f1 12646 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12646 : ℝ) ^ 8 * (mA 12646 : ℝ) ^ 8 *
        ((((463178507 / 100000000000000000) : ℝ) ^ 2 + 2 * ((463178507 / 100000000000000000)) * ((1545241823 / 1000000000000000000)) * (126 / 100) +
          2 * (((1545241823 / 1000000000000000000)) ^ 2 + 2 * ((463178507 / 100000000000000000)) * ((371399411 / 1000000000000000000))) +
          6 * ((1545241823 / 1000000000000000000)) * ((371399411 / 1000000000000000000)) * (126 / 100) + 8 * ((371399411 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12646) *
          (32 * (((463178507 / 100000000000000000) : ℝ) + (1545241823 / 1000000000000000000) + (371399411 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12646 : ℝ) ^ 16 *
      (d.w0 12646 162 + d.w1 12646 162 * √(π / 2) + 2 * d.w2 12646 162 +
        energyR16 12646 * radiusPolynomialRoot16 (d.w0 12646 162) (d.w1 12646 162)
          (d.w2 12646 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12646 : ℝ) ^ 16 *
        (((1856785163 / 100000000000000000000) : ℝ) + ((1321067121 / 100000000000000000000)) * (126 / 100) + 2 * ((120671191 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12646) *
          (32 * (((1856785163 / 100000000000000000000) : ℝ) + (1321067121 / 100000000000000000000) + (120671191 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12646

/-! A coarse bound on the actual paper statistics constant at dimension 12647. -/
namespace BstLean.Part266.Row12647
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12645 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12645 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12645 128 ≤ (12899 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12899 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12647) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12647 : ℕ))
    (by norm_num : (12647 : ℕ) ≤ 16384)
  have ht : paperTail256 12647 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12647 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12647 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12647 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12647 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12647 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12645 128 * √(2 / (12647 : ℝ)) *
      (√(12647 : ℝ) + paperT0 12647 + paperTail256 12647) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12647 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12647 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12647 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12645 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12645 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12647 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12647

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12647
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12647 (61 / 100) 162 (17 / (100 * 12647)) (26 / (10 * 12647)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12647 (61 / 100) 162 (17 / (100 * 12647)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (241282571 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (763129831 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5290813161 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12647 / 12647 * (61 / 100)) ^ 4 * inverseRadius8 (12647 - 1) /
            envelopeGap 12647 (61 / 100) 162 (17 / (100 * 12647)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12647

namespace BstLean.Part266.Row12647
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12647 162 ≤ (4630869633 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12647 162 ≤ (772468201 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (371325999 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12647 162 ≤ (928172379 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12647 162 ≤ (660376887 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12647 162 ≤ (120642567 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (241282571 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (241282571 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (763129831 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5290813161 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1833161 / 500000000) : ℝ) ≤ √(17 / (100 * 12647) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12647) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2196736539 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3906737337 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12647) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12647) ≤ (55911029 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12647) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12647 * (162 : ℝ) ^ 2 + 26 / (10 * 12647) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12647) : ℝ)) (tA 12647 * 162 ^ 2 + 26 / (10 * 12647)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1833161 / 500000000))) * ((241282571 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1833161 / 500000000)) ^ 3) * ((763129831 / 500000000000000000000000))) + ((5290813161 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1833161 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12647) : ℝ)) d.D d.V d.P (√(tA 12647) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1833161 / 500000000)) ^ 2 * (((2196736539 / 1000000000000000)) * ((3906737337 / 100000000000000000)))) + ((5290813161 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12647) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1833161 / 500000000)) * ((241282571 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12647) : ℝ)) (tA 12647 * 162 ^ 2 + 26 / (10 * 12647)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((241282571 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1833161 / 500000000)) ^ 2) * ((763129831 / 500000000000000000000000)) + ((5290813161 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12647) : ℝ)) (√(26 / (10 * 12647) : ℝ)) d.D d.V d.P (√(tA 12647) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1833161 / 500000000)) * (((2196736539 / 1000000000000000)) * ((3906737337 / 100000000000000000))) + ((5290813161 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12647) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((241282571 / 50000000000000000000) : ℝ) + ((5290813161 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12647

namespace BstLean.Part266.Row12647
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12647 162 ∧
    0 ≤ (tableEnvelope C).f1 12647 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12647 162 ∧
    0 ≤ (tableEnvelope C).w1 12647 162 ∧ 0 ≤ (tableEnvelope C).w2 12647 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12647 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12647 162 ∧ 0 ≤ d.f1 12647 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12647 162 ∧ 0 ≤ d.w1 12647 162 ∧ 0 ≤ d.w2 12647 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12647 ≤ 2 * (228 / 100 : ℝ) / 12647 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12647 ≤ 2 * (370 / 100 : ℝ) / 12647 := by
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
    (completeRAData (tableEnvelope C) 12647 162).locationBound 12647 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12647 162).energyBound 12647 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12647 162) (d.f1 12647 162) d.f2 ≤
      32 * (((4630869633 / 1000000000000000000) : ℝ) + (772468201 / 500000000000000000) + (371325999 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12647 162) (d.w1 12647 162)
      (d.w2 12647 162) ≤
      32 * (((928172379 / 50000000000000000000) : ℝ) + (660376887 / 50000000000000000000) + (120642567 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12647 162) (d.f1 12647 162) d.f2 ≤
      ((4630869633 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4630869633 / 1000000000000000000)) * ((772468201 / 500000000000000000)) * (126 / 100) +
      2 * (((772468201 / 500000000000000000)) ^ 2 + 2 * ((4630869633 / 1000000000000000000)) * ((371325999 / 1000000000000000000))) +
      6 * ((772468201 / 500000000000000000)) * ((371325999 / 1000000000000000000)) * (126 / 100) + 8 * ((371325999 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12647 162) (d.f1 12647 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12647 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12647 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12647 162) (d.f1 12647 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12647 162) (d.w1 12647 162) (d.w2 12647 162)
  have hwexpr0 : 0 ≤ d.w0 12647 162 + d.w1 12647 162 * √(π / 2) +
      2 * d.w2 12647 162 + energyR16 12647 *
      radiusPolynomialRoot16 (d.w0 12647 162) (d.w1 12647 162) (d.w2 12647 162) := by
    positivity
  constructor
  · change (12647 : ℝ) ^ 8 * (mA 12647 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12647 162) (d.f1 12647 162) d.f2 + locationR16 12647 *
        radiusPolynomialRoot16 (d.f0 12647 162) (d.f1 12647 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12647 : ℝ) ^ 8 * (mA 12647 : ℝ) ^ 8 *
        ((((4630869633 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4630869633 / 1000000000000000000)) * ((772468201 / 500000000000000000)) * (126 / 100) +
          2 * (((772468201 / 500000000000000000)) ^ 2 + 2 * ((4630869633 / 1000000000000000000)) * ((371325999 / 1000000000000000000))) +
          6 * ((772468201 / 500000000000000000)) * ((371325999 / 1000000000000000000)) * (126 / 100) + 8 * ((371325999 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12647) *
          (32 * (((4630869633 / 1000000000000000000) : ℝ) + (772468201 / 500000000000000000) + (371325999 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12647 : ℝ) ^ 16 *
      (d.w0 12647 162 + d.w1 12647 162 * √(π / 2) + 2 * d.w2 12647 162 +
        energyR16 12647 * radiusPolynomialRoot16 (d.w0 12647 162) (d.w1 12647 162)
          (d.w2 12647 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12647 : ℝ) ^ 16 *
        (((928172379 / 50000000000000000000) : ℝ) + ((660376887 / 50000000000000000000)) * (126 / 100) + 2 * ((120642567 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12647) *
          (32 * (((928172379 / 50000000000000000000) : ℝ) + (660376887 / 50000000000000000000) + (120642567 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12647

/-! A coarse bound on the actual paper statistics constant at dimension 12648. -/
namespace BstLean.Part266.Row12648
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12646 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12646 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12646 128 ≤ (12900 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12900 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12648) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12648 : ℕ))
    (by norm_num : (12648 : ℕ) ≤ 16384)
  have ht : paperTail256 12648 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12648 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12648 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12648 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12648 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12648 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12646 128 * √(2 / (12648 : ℝ)) *
      (√(12648 : ℝ) + paperT0 12648 + paperTail256 12648) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12648 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12648 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12648 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12646 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12646 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12648 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12648

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12648
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12648 (61 / 100) 162 (17 / (100 * 12648)) (26 / (10 * 12648)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12648 (61 / 100) 162 (17 / (100 * 12648)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (120612671 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1525777013 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (41308087 / 7812500000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12648 / 12648 * (61 / 100)) ^ 4 * inverseRadius8 (12648 - 1) /
            envelopeGap 12648 (61 / 100) 162 (17 / (100 * 12648)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12648

namespace BstLean.Part266.Row12648
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12648 162 ≤ (925990903 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12648 162 ≤ (1544631079 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (2900411 / 7812500000000000)
  w0 : (tableEnvelope C).w0 12648 162 ≤ (371180901 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12648 162 ≤ (1320440531 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12648 162 ≤ (241227903 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (120612671 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (120612671 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1525777013 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (41308087 / 7812500000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3666177 / 1000000000) : ℝ) ≤ √(17 / (100 * 12648) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12648) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (439295201 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7812239149 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12648) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12648) ≤ (111813217 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12648) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12648 * (162 : ℝ) ^ 2 + 26 / (10 * 12648) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12648) : ℝ)) (tA 12648 * 162 ^ 2 + 26 / (10 * 12648)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3666177 / 1000000000))) * ((120612671 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3666177 / 1000000000)) ^ 3) * ((1525777013 / 1000000000000000000000000))) + ((41308087 / 7812500000000000000000)) * (3 / 2 * (39895 / 100000) / ((3666177 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12648) : ℝ)) d.D d.V d.P (√(tA 12648) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3666177 / 1000000000)) ^ 2 * (((439295201 / 200000000000000)) * ((7812239149 / 200000000000000000)))) + ((41308087 / 7812500000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12648) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3666177 / 1000000000)) * ((120612671 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12648) : ℝ)) (tA 12648 * 162 ^ 2 + 26 / (10 * 12648)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((120612671 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3666177 / 1000000000)) ^ 2) * ((1525777013 / 1000000000000000000000000)) + ((41308087 / 7812500000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12648) : ℝ)) (√(26 / (10 * 12648) : ℝ)) d.D d.V d.P (√(tA 12648) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3666177 / 1000000000)) * (((439295201 / 200000000000000)) * ((7812239149 / 200000000000000000))) + ((41308087 / 7812500000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12648) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((120612671 / 25000000000000000000) : ℝ) + ((41308087 / 7812500000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12648

namespace BstLean.Part266.Row12648
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12648 162 ∧
    0 ≤ (tableEnvelope C).f1 12648 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12648 162 ∧
    0 ≤ (tableEnvelope C).w1 12648 162 ∧ 0 ≤ (tableEnvelope C).w2 12648 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12648 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12648 162 ∧ 0 ≤ d.f1 12648 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12648 162 ∧ 0 ≤ d.w1 12648 162 ∧ 0 ≤ d.w2 12648 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12648 ≤ 2 * (228 / 100 : ℝ) / 12648 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12648 ≤ 2 * (370 / 100 : ℝ) / 12648 := by
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
    (completeRAData (tableEnvelope C) 12648 162).locationBound 12648 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12648 162).energyBound 12648 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12648 162) (d.f1 12648 162) d.f2 ≤
      32 * (((925990903 / 200000000000000000) : ℝ) + (1544631079 / 1000000000000000000) + (2900411 / 7812500000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12648 162) (d.w1 12648 162)
      (d.w2 12648 162) ≤
      32 * (((371180901 / 20000000000000000000) : ℝ) + (1320440531 / 100000000000000000000) + (241227903 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12648 162) (d.f1 12648 162) d.f2 ≤
      ((925990903 / 200000000000000000) : ℝ) ^ 2 + 2 * ((925990903 / 200000000000000000)) * ((1544631079 / 1000000000000000000)) * (126 / 100) +
      2 * (((1544631079 / 1000000000000000000)) ^ 2 + 2 * ((925990903 / 200000000000000000)) * ((2900411 / 7812500000000000))) +
      6 * ((1544631079 / 1000000000000000000)) * ((2900411 / 7812500000000000)) * (126 / 100) + 8 * ((2900411 / 7812500000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12648 162) (d.f1 12648 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12648 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12648 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12648 162) (d.f1 12648 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12648 162) (d.w1 12648 162) (d.w2 12648 162)
  have hwexpr0 : 0 ≤ d.w0 12648 162 + d.w1 12648 162 * √(π / 2) +
      2 * d.w2 12648 162 + energyR16 12648 *
      radiusPolynomialRoot16 (d.w0 12648 162) (d.w1 12648 162) (d.w2 12648 162) := by
    positivity
  constructor
  · change (12648 : ℝ) ^ 8 * (mA 12648 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12648 162) (d.f1 12648 162) d.f2 + locationR16 12648 *
        radiusPolynomialRoot16 (d.f0 12648 162) (d.f1 12648 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12648 : ℝ) ^ 8 * (mA 12648 : ℝ) ^ 8 *
        ((((925990903 / 200000000000000000) : ℝ) ^ 2 + 2 * ((925990903 / 200000000000000000)) * ((1544631079 / 1000000000000000000)) * (126 / 100) +
          2 * (((1544631079 / 1000000000000000000)) ^ 2 + 2 * ((925990903 / 200000000000000000)) * ((2900411 / 7812500000000000))) +
          6 * ((1544631079 / 1000000000000000000)) * ((2900411 / 7812500000000000)) * (126 / 100) + 8 * ((2900411 / 7812500000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12648) *
          (32 * (((925990903 / 200000000000000000) : ℝ) + (1544631079 / 1000000000000000000) + (2900411 / 7812500000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12648 : ℝ) ^ 16 *
      (d.w0 12648 162 + d.w1 12648 162 * √(π / 2) + 2 * d.w2 12648 162 +
        energyR16 12648 * radiusPolynomialRoot16 (d.w0 12648 162) (d.w1 12648 162)
          (d.w2 12648 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12648 : ℝ) ^ 16 *
        (((371180901 / 20000000000000000000) : ℝ) + ((1320440531 / 100000000000000000000)) * (126 / 100) + 2 * ((241227903 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12648) *
          (32 * (((371180901 / 20000000000000000000) : ℝ) + (1320440531 / 100000000000000000000) + (241227903 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12648

/-! A coarse bound on the actual paper statistics constant at dimension 12649. -/
namespace BstLean.Part266.Row12649
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12647 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12647 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12647 128 ≤ (12901 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12901 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12649) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12649 : ℕ))
    (by norm_num : (12649 : ℕ) ≤ 16384)
  have ht : paperTail256 12649 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12649 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12649 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12649 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12649 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12649 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12647 128 * √(2 / (12649 : ℝ)) *
      (√(12649 : ℝ) + paperT0 12649 + paperTail256 12649) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12649 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12649 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12649 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12647 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12647 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12649 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12649

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12649
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12649 (61 / 100) 162 (17 / (100 * 12649)) (26 / (10 * 12649)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12649 (61 / 100) 162 (17 / (100 * 12649)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (482336263 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1525294553 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5284059539 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12649 / 12649 * (61 / 100)) ^ 4 * inverseRadius8 (12649 - 1) /
            envelopeGap 12649 (61 / 100) 162 (17 / (100 * 12649)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12649

namespace BstLean.Part266.Row12649
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12649 162 ≤ (4629039709 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12649 162 ≤ (48260183 / 31250000000000000)
  f2 : (tableEnvelope C).f2 ≤ (9279481 / 25000000000000000)
  w0 : (tableEnvelope C).w0 12649 162 ≤ (463866101 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12649 162 ≤ (264025479 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12649 162 ≤ (241170691 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (482336263 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (482336263 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1525294553 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5284059539 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((229127 / 62500000) : ℝ) ≤ √(17 / (100 * 12649) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12649) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (87848621 / 40000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39055019563 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12649) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12649) ≤ (111804377 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12649) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12649 * (162 : ℝ) ^ 2 + 26 / (10 * 12649) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12649) : ℝ)) (tA 12649 * 162 ^ 2 + 26 / (10 * 12649)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((229127 / 62500000))) * ((482336263 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((229127 / 62500000)) ^ 3) * ((1525294553 / 1000000000000000000000000))) + ((5284059539 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((229127 / 62500000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12649) : ℝ)) d.D d.V d.P (√(tA 12649) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((229127 / 62500000)) ^ 2 * (((87848621 / 40000000000000)) * ((39055019563 / 1000000000000000000)))) + ((5284059539 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12649) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((229127 / 62500000)) * ((482336263 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12649) : ℝ)) (tA 12649 * 162 ^ 2 + 26 / (10 * 12649)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((482336263 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((229127 / 62500000)) ^ 2) * ((1525294553 / 1000000000000000000000000)) + ((5284059539 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12649) : ℝ)) (√(26 / (10 * 12649) : ℝ)) d.D d.V d.P (√(tA 12649) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((229127 / 62500000)) * (((87848621 / 40000000000000)) * ((39055019563 / 1000000000000000000))) + ((5284059539 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12649) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((482336263 / 100000000000000000000) : ℝ) + ((5284059539 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12649

namespace BstLean.Part266.Row12649
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12649 162 ∧
    0 ≤ (tableEnvelope C).f1 12649 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12649 162 ∧
    0 ≤ (tableEnvelope C).w1 12649 162 ∧ 0 ≤ (tableEnvelope C).w2 12649 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12649 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12649 162 ∧ 0 ≤ d.f1 12649 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12649 162 ∧ 0 ≤ d.w1 12649 162 ∧ 0 ≤ d.w2 12649 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12649 ≤ 2 * (228 / 100 : ℝ) / 12649 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12649 ≤ 2 * (370 / 100 : ℝ) / 12649 := by
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
    (completeRAData (tableEnvelope C) 12649 162).locationBound 12649 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12649 162).energyBound 12649 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12649 162) (d.f1 12649 162) d.f2 ≤
      32 * (((4629039709 / 1000000000000000000) : ℝ) + (48260183 / 31250000000000000) + (9279481 / 25000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12649 162) (d.w1 12649 162)
      (d.w2 12649 162) ≤
      32 * (((463866101 / 25000000000000000000) : ℝ) + (264025479 / 20000000000000000000) + (241170691 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12649 162) (d.f1 12649 162) d.f2 ≤
      ((4629039709 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4629039709 / 1000000000000000000)) * ((48260183 / 31250000000000000)) * (126 / 100) +
      2 * (((48260183 / 31250000000000000)) ^ 2 + 2 * ((4629039709 / 1000000000000000000)) * ((9279481 / 25000000000000000))) +
      6 * ((48260183 / 31250000000000000)) * ((9279481 / 25000000000000000)) * (126 / 100) + 8 * ((9279481 / 25000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12649 162) (d.f1 12649 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12649 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12649 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12649 162) (d.f1 12649 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12649 162) (d.w1 12649 162) (d.w2 12649 162)
  have hwexpr0 : 0 ≤ d.w0 12649 162 + d.w1 12649 162 * √(π / 2) +
      2 * d.w2 12649 162 + energyR16 12649 *
      radiusPolynomialRoot16 (d.w0 12649 162) (d.w1 12649 162) (d.w2 12649 162) := by
    positivity
  constructor
  · change (12649 : ℝ) ^ 8 * (mA 12649 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12649 162) (d.f1 12649 162) d.f2 + locationR16 12649 *
        radiusPolynomialRoot16 (d.f0 12649 162) (d.f1 12649 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12649 : ℝ) ^ 8 * (mA 12649 : ℝ) ^ 8 *
        ((((4629039709 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4629039709 / 1000000000000000000)) * ((48260183 / 31250000000000000)) * (126 / 100) +
          2 * (((48260183 / 31250000000000000)) ^ 2 + 2 * ((4629039709 / 1000000000000000000)) * ((9279481 / 25000000000000000))) +
          6 * ((48260183 / 31250000000000000)) * ((9279481 / 25000000000000000)) * (126 / 100) + 8 * ((9279481 / 25000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12649) *
          (32 * (((4629039709 / 1000000000000000000) : ℝ) + (48260183 / 31250000000000000) + (9279481 / 25000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12649 : ℝ) ^ 16 *
      (d.w0 12649 162 + d.w1 12649 162 * √(π / 2) + 2 * d.w2 12649 162 +
        energyR16 12649 * radiusPolynomialRoot16 (d.w0 12649 162) (d.w1 12649 162)
          (d.w2 12649 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12649 : ℝ) ^ 16 *
        (((463866101 / 25000000000000000000) : ℝ) + ((264025479 / 20000000000000000000)) * (126 / 100) + 2 * ((241170691 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12649) *
          (32 * (((463866101 / 25000000000000000000) : ℝ) + (264025479 / 20000000000000000000) + (241170691 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12649
