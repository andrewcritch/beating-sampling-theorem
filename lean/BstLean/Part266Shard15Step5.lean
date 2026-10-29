import BstLean.Part266Shard15Step4


/-! A coarse bound on the actual paper statistics constant at dimension 12725. -/
namespace BstLean.Part266.Row12725
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12723 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12723 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12723 128 ≤ (12977 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12977 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12725) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12725 : ℕ))
    (by norm_num : (12725 : ℕ) ≤ 16384)
  have ht : paperTail256 12725 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12725 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12725 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12725 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12725 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12725 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12723 128 * √(2 / (12725 : ℝ)) *
      (√(12725 : ℝ) + paperT0 12725 + paperTail256 12725) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12725 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12725 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12725 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12723 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12723 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12725 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12725

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12725
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12725 (61 / 100) 163 (17 / (100 * 12725)) (26 / (10 * 12725)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12725 (61 / 100) 163 (17 / (100 * 12725)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (118436269 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (744589521 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5036807473 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12725 / 12725 * (61 / 100)) ^ 4 * inverseRadius8 (12725 - 1) /
            envelopeGap 12725 (61 / 100) 163 (17 / (100 * 12725)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12725

namespace BstLean.Part266.Row12725
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12725 163 ≤ (2280113561 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12725 163 ≤ (1521368829 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (365661523 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12725 163 ≤ (3644831 / 200000000000000000)
  w1 : (tableEnvelope C).w1 12725 163 ≤ (648306873 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12725 163 ≤ (118437489 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (118436269 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (118436269 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (744589521 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5036807473 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((913767 / 250000000) : ℝ) ≤ √(17 / (100 * 12725) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12725) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (87062743 / 40000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19294941319 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12725) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12725) ≤ (55568313 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12725) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12725 * (163 : ℝ) ^ 2 + 26 / (10 * 12725) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12725) : ℝ)) (tA 12725 * 163 ^ 2 + 26 / (10 * 12725)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((913767 / 250000000))) * ((118436269 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((913767 / 250000000)) ^ 3) * ((744589521 / 500000000000000000000000))) + ((5036807473 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((913767 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12725) : ℝ)) d.D d.V d.P (√(tA 12725) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((913767 / 250000000)) ^ 2 * (((87062743 / 40000000000000)) * ((19294941319 / 500000000000000000)))) + ((5036807473 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12725) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((913767 / 250000000)) * ((118436269 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12725) : ℝ)) (tA 12725 * 163 ^ 2 + 26 / (10 * 12725)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((118436269 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((913767 / 250000000)) ^ 2) * ((744589521 / 500000000000000000000000)) + ((5036807473 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12725) : ℝ)) (√(26 / (10 * 12725) : ℝ)) d.D d.V d.P (√(tA 12725) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((913767 / 250000000)) * (((87062743 / 40000000000000)) * ((19294941319 / 500000000000000000))) + ((5036807473 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12725) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((118436269 / 25000000000000000000) : ℝ) + ((5036807473 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12725

namespace BstLean.Part266.Row12725
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12725 163 ∧
    0 ≤ (tableEnvelope C).f1 12725 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12725 163 ∧
    0 ≤ (tableEnvelope C).w1 12725 163 ∧ 0 ≤ (tableEnvelope C).w2 12725 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12725 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12725 163 ∧ 0 ≤ d.f1 12725 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12725 163 ∧ 0 ≤ d.w1 12725 163 ∧ 0 ≤ d.w2 12725 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12725 ≤ 2 * (228 / 100 : ℝ) / 12725 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12725 ≤ 2 * (370 / 100 : ℝ) / 12725 := by
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
    (completeRAData (tableEnvelope C) 12725 163).locationBound 12725 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12725 163).energyBound 12725 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12725 163) (d.f1 12725 163) d.f2 ≤
      32 * (((2280113561 / 500000000000000000) : ℝ) + (1521368829 / 1000000000000000000) + (365661523 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12725 163) (d.w1 12725 163)
      (d.w2 12725 163) ≤
      32 * (((3644831 / 200000000000000000) : ℝ) + (648306873 / 50000000000000000000) + (118437489 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12725 163) (d.f1 12725 163) d.f2 ≤
      ((2280113561 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2280113561 / 500000000000000000)) * ((1521368829 / 1000000000000000000)) * (126 / 100) +
      2 * (((1521368829 / 1000000000000000000)) ^ 2 + 2 * ((2280113561 / 500000000000000000)) * ((365661523 / 1000000000000000000))) +
      6 * ((1521368829 / 1000000000000000000)) * ((365661523 / 1000000000000000000)) * (126 / 100) + 8 * ((365661523 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12725 163) (d.f1 12725 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12725 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12725 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12725 163) (d.f1 12725 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12725 163) (d.w1 12725 163) (d.w2 12725 163)
  have hwexpr0 : 0 ≤ d.w0 12725 163 + d.w1 12725 163 * √(π / 2) +
      2 * d.w2 12725 163 + energyR16 12725 *
      radiusPolynomialRoot16 (d.w0 12725 163) (d.w1 12725 163) (d.w2 12725 163) := by
    positivity
  constructor
  · change (12725 : ℝ) ^ 8 * (mA 12725 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12725 163) (d.f1 12725 163) d.f2 + locationR16 12725 *
        radiusPolynomialRoot16 (d.f0 12725 163) (d.f1 12725 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12725 : ℝ) ^ 8 * (mA 12725 : ℝ) ^ 8 *
        ((((2280113561 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2280113561 / 500000000000000000)) * ((1521368829 / 1000000000000000000)) * (126 / 100) +
          2 * (((1521368829 / 1000000000000000000)) ^ 2 + 2 * ((2280113561 / 500000000000000000)) * ((365661523 / 1000000000000000000))) +
          6 * ((1521368829 / 1000000000000000000)) * ((365661523 / 1000000000000000000)) * (126 / 100) + 8 * ((365661523 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12725) *
          (32 * (((2280113561 / 500000000000000000) : ℝ) + (1521368829 / 1000000000000000000) + (365661523 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12725 : ℝ) ^ 16 *
      (d.w0 12725 163 + d.w1 12725 163 * √(π / 2) + 2 * d.w2 12725 163 +
        energyR16 12725 * radiusPolynomialRoot16 (d.w0 12725 163) (d.w1 12725 163)
          (d.w2 12725 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12725 : ℝ) ^ 16 *
        (((3644831 / 200000000000000000) : ℝ) + ((648306873 / 50000000000000000000)) * (126 / 100) + 2 * ((118437489 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12725) *
          (32 * (((3644831 / 200000000000000000) : ℝ) + (648306873 / 50000000000000000000) + (118437489 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12725

/-! A coarse bound on the actual paper statistics constant at dimension 12726. -/
namespace BstLean.Part266.Row12726
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12724 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12724 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12724 128 ≤ (12978 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12978 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12726) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12726 : ℕ))
    (by norm_num : (12726 : ℕ) ≤ 16384)
  have ht : paperTail256 12726 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12726 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12726 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12726 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12726 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12726 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12724 128 * √(2 / (12726 : ℝ)) *
      (√(12726 : ℝ) + paperT0 12726 + paperTail256 12726) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12726 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12726 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12726 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12724 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12724 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12726 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12726

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12726
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12726 (61 / 100) 163 (17 / (100 * 12726)) (26 / (10 * 12726)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12726 (61 / 100) 163 (17 / (100 * 12726)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (473633399 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (372177751 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1258402833 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12726 / 12726 * (61 / 100)) ^ 4 * inverseRadius8 (12726 - 1) /
            envelopeGap 12726 (61 / 100) 163 (17 / (100 * 12726)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12726

namespace BstLean.Part266.Row12726
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12726 163 ≤ (1139832269 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12726 163 ≤ (30421389 / 20000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (91397407 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12726 163 ≤ (227748181 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 12726 163 ≤ (324076969 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12726 163 ≤ (18945531 / 4000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (473633399 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (473633399 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (372177751 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1258402833 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((146197 / 40000000) : ℝ) ≤ √(17 / (100 * 12726) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12726) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (136019501 / 62500000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (2411488619 / 62500000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12726) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12726) ≤ (111127893 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12726) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12726 * (163 : ℝ) ^ 2 + 26 / (10 * 12726) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12726) : ℝ)) (tA 12726 * 163 ^ 2 + 26 / (10 * 12726)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((146197 / 40000000))) * ((473633399 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((146197 / 40000000)) ^ 3) * ((372177751 / 250000000000000000000000))) + ((1258402833 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((146197 / 40000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12726) : ℝ)) d.D d.V d.P (√(tA 12726) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((146197 / 40000000)) ^ 2 * (((136019501 / 62500000000000)) * ((2411488619 / 62500000000000000)))) + ((1258402833 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12726) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((146197 / 40000000)) * ((473633399 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12726) : ℝ)) (tA 12726 * 163 ^ 2 + 26 / (10 * 12726)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((473633399 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((146197 / 40000000)) ^ 2) * ((372177751 / 250000000000000000000000)) + ((1258402833 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12726) : ℝ)) (√(26 / (10 * 12726) : ℝ)) d.D d.V d.P (√(tA 12726) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((146197 / 40000000)) * (((136019501 / 62500000000000)) * ((2411488619 / 62500000000000000))) + ((1258402833 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12726) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((473633399 / 100000000000000000000) : ℝ) + ((1258402833 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12726

namespace BstLean.Part266.Row12726
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12726 163 ∧
    0 ≤ (tableEnvelope C).f1 12726 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12726 163 ∧
    0 ≤ (tableEnvelope C).w1 12726 163 ∧ 0 ≤ (tableEnvelope C).w2 12726 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12726 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12726 163 ∧ 0 ≤ d.f1 12726 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12726 163 ∧ 0 ≤ d.w1 12726 163 ∧ 0 ≤ d.w2 12726 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12726 ≤ 2 * (228 / 100 : ℝ) / 12726 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12726 ≤ 2 * (370 / 100 : ℝ) / 12726 := by
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
    (completeRAData (tableEnvelope C) 12726 163).locationBound 12726 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12726 163).energyBound 12726 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12726 163) (d.f1 12726 163) d.f2 ≤
      32 * (((1139832269 / 250000000000000000) : ℝ) + (30421389 / 20000000000000000) + (91397407 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12726 163) (d.w1 12726 163)
      (d.w2 12726 163) ≤
      32 * (((227748181 / 12500000000000000000) : ℝ) + (324076969 / 25000000000000000000) + (18945531 / 4000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12726 163) (d.f1 12726 163) d.f2 ≤
      ((1139832269 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1139832269 / 250000000000000000)) * ((30421389 / 20000000000000000)) * (126 / 100) +
      2 * (((30421389 / 20000000000000000)) ^ 2 + 2 * ((1139832269 / 250000000000000000)) * ((91397407 / 250000000000000000))) +
      6 * ((30421389 / 20000000000000000)) * ((91397407 / 250000000000000000)) * (126 / 100) + 8 * ((91397407 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12726 163) (d.f1 12726 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12726 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12726 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12726 163) (d.f1 12726 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12726 163) (d.w1 12726 163) (d.w2 12726 163)
  have hwexpr0 : 0 ≤ d.w0 12726 163 + d.w1 12726 163 * √(π / 2) +
      2 * d.w2 12726 163 + energyR16 12726 *
      radiusPolynomialRoot16 (d.w0 12726 163) (d.w1 12726 163) (d.w2 12726 163) := by
    positivity
  constructor
  · change (12726 : ℝ) ^ 8 * (mA 12726 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12726 163) (d.f1 12726 163) d.f2 + locationR16 12726 *
        radiusPolynomialRoot16 (d.f0 12726 163) (d.f1 12726 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12726 : ℝ) ^ 8 * (mA 12726 : ℝ) ^ 8 *
        ((((1139832269 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1139832269 / 250000000000000000)) * ((30421389 / 20000000000000000)) * (126 / 100) +
          2 * (((30421389 / 20000000000000000)) ^ 2 + 2 * ((1139832269 / 250000000000000000)) * ((91397407 / 250000000000000000))) +
          6 * ((30421389 / 20000000000000000)) * ((91397407 / 250000000000000000)) * (126 / 100) + 8 * ((91397407 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12726) *
          (32 * (((1139832269 / 250000000000000000) : ℝ) + (30421389 / 20000000000000000) + (91397407 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12726 : ℝ) ^ 16 *
      (d.w0 12726 163 + d.w1 12726 163 * √(π / 2) + 2 * d.w2 12726 163 +
        energyR16 12726 * radiusPolynomialRoot16 (d.w0 12726 163) (d.w1 12726 163)
          (d.w2 12726 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12726 : ℝ) ^ 16 *
        (((227748181 / 12500000000000000000) : ℝ) + ((324076969 / 25000000000000000000)) * (126 / 100) + 2 * ((18945531 / 4000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12726) *
          (32 * (((227748181 / 12500000000000000000) : ℝ) + (324076969 / 25000000000000000000) + (18945531 / 4000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12726

/-! A coarse bound on the actual paper statistics constant at dimension 12727. -/
namespace BstLean.Part266.Row12727
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12725 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12725 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12725 128 ≤ (12979 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12979 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12727) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12727 : ℕ))
    (by norm_num : (12727 : ℕ) ≤ 16384)
  have ht : paperTail256 12727 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12727 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12727 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12727 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12727 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12727 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12725 128 * √(2 / (12727 : ℝ)) *
      (√(12727 : ℝ) + paperT0 12727 + paperTail256 12727) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12727 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12727 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12727 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12725 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12725 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12727 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12727

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12727
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12727 (61 / 100) 163 (17 / (100 * 12727)) (26 / (10 * 12727)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12727 (61 / 100) 163 (17 / (100 * 12727)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (236760879 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (29764863 / 20000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2515208737 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12727 / 12727 * (61 / 100)) ^ 4 * inverseRadius8 (12727 - 1) /
            envelopeGap 12727 (61 / 100) 163 (17 / (100 * 12727)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12727

namespace BstLean.Part266.Row12727
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12727 163 ≤ (2279217469 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12727 163 ≤ (1520771001 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (73103571 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12727 163 ≤ (1821556283 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12727 163 ≤ (40500077 / 3125000000000000000)
  w2 : (tableEnvelope C).w2 12727 163 ≤ (473526631 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (236760879 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (236760879 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (29764863 / 20000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2515208737 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3654781 / 1000000000) : ℝ) ≤ √(17 / (100 * 12727) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12727) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (217605551 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38577754601 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12727) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12727) ≤ (55559581 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12727) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12727 * (163 : ℝ) ^ 2 + 26 / (10 * 12727) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12727) : ℝ)) (tA 12727 * 163 ^ 2 + 26 / (10 * 12727)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3654781 / 1000000000))) * ((236760879 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3654781 / 1000000000)) ^ 3) * ((29764863 / 20000000000000000000000))) + ((2515208737 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3654781 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12727) : ℝ)) d.D d.V d.P (√(tA 12727) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3654781 / 1000000000)) ^ 2 * (((217605551 / 100000000000000)) * ((38577754601 / 1000000000000000000)))) + ((2515208737 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12727) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3654781 / 1000000000)) * ((236760879 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12727) : ℝ)) (tA 12727 * 163 ^ 2 + 26 / (10 * 12727)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((236760879 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3654781 / 1000000000)) ^ 2) * ((29764863 / 20000000000000000000000)) + ((2515208737 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12727) : ℝ)) (√(26 / (10 * 12727) : ℝ)) d.D d.V d.P (√(tA 12727) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3654781 / 1000000000)) * (((217605551 / 100000000000000)) * ((38577754601 / 1000000000000000000))) + ((2515208737 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12727) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((236760879 / 50000000000000000000) : ℝ) + ((2515208737 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12727

namespace BstLean.Part266.Row12727
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12727 163 ∧
    0 ≤ (tableEnvelope C).f1 12727 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12727 163 ∧
    0 ≤ (tableEnvelope C).w1 12727 163 ∧ 0 ≤ (tableEnvelope C).w2 12727 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12727 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12727 163 ∧ 0 ≤ d.f1 12727 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12727 163 ∧ 0 ≤ d.w1 12727 163 ∧ 0 ≤ d.w2 12727 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12727 ≤ 2 * (228 / 100 : ℝ) / 12727 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12727 ≤ 2 * (370 / 100 : ℝ) / 12727 := by
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
    (completeRAData (tableEnvelope C) 12727 163).locationBound 12727 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12727 163).energyBound 12727 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12727 163) (d.f1 12727 163) d.f2 ≤
      32 * (((2279217469 / 500000000000000000) : ℝ) + (1520771001 / 1000000000000000000) + (73103571 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12727 163) (d.w1 12727 163)
      (d.w2 12727 163) ≤
      32 * (((1821556283 / 100000000000000000000) : ℝ) + (40500077 / 3125000000000000000) + (473526631 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12727 163) (d.f1 12727 163) d.f2 ≤
      ((2279217469 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2279217469 / 500000000000000000)) * ((1520771001 / 1000000000000000000)) * (126 / 100) +
      2 * (((1520771001 / 1000000000000000000)) ^ 2 + 2 * ((2279217469 / 500000000000000000)) * ((73103571 / 200000000000000000))) +
      6 * ((1520771001 / 1000000000000000000)) * ((73103571 / 200000000000000000)) * (126 / 100) + 8 * ((73103571 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12727 163) (d.f1 12727 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12727 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12727 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12727 163) (d.f1 12727 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12727 163) (d.w1 12727 163) (d.w2 12727 163)
  have hwexpr0 : 0 ≤ d.w0 12727 163 + d.w1 12727 163 * √(π / 2) +
      2 * d.w2 12727 163 + energyR16 12727 *
      radiusPolynomialRoot16 (d.w0 12727 163) (d.w1 12727 163) (d.w2 12727 163) := by
    positivity
  constructor
  · change (12727 : ℝ) ^ 8 * (mA 12727 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12727 163) (d.f1 12727 163) d.f2 + locationR16 12727 *
        radiusPolynomialRoot16 (d.f0 12727 163) (d.f1 12727 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12727 : ℝ) ^ 8 * (mA 12727 : ℝ) ^ 8 *
        ((((2279217469 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2279217469 / 500000000000000000)) * ((1520771001 / 1000000000000000000)) * (126 / 100) +
          2 * (((1520771001 / 1000000000000000000)) ^ 2 + 2 * ((2279217469 / 500000000000000000)) * ((73103571 / 200000000000000000))) +
          6 * ((1520771001 / 1000000000000000000)) * ((73103571 / 200000000000000000)) * (126 / 100) + 8 * ((73103571 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12727) *
          (32 * (((2279217469 / 500000000000000000) : ℝ) + (1520771001 / 1000000000000000000) + (73103571 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12727 : ℝ) ^ 16 *
      (d.w0 12727 163 + d.w1 12727 163 * √(π / 2) + 2 * d.w2 12727 163 +
        energyR16 12727 * radiusPolynomialRoot16 (d.w0 12727 163) (d.w1 12727 163)
          (d.w2 12727 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12727 : ℝ) ^ 16 *
        (((1821556283 / 100000000000000000000) : ℝ) + ((40500077 / 3125000000000000000)) * (126 / 100) + 2 * ((473526631 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12727) *
          (32 * (((1821556283 / 100000000000000000000) : ℝ) + (40500077 / 3125000000000000000) + (473526631 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12727

/-! A coarse bound on the actual paper statistics constant at dimension 12728. -/
namespace BstLean.Part266.Row12728
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12726 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12726 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12726 128 ≤ (12980 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12980 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12728) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12728 : ℕ))
    (by norm_num : (12728 : ℕ) ≤ 16384)
  have ht : paperTail256 12728 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12728 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12728 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12728 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12728 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12728 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12726 128 * √(2 / (12728 : ℝ)) *
      (√(12728 : ℝ) + paperT0 12728 + paperTail256 12728) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12728 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12728 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12728 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12726 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12726 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12728 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12728

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12728
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12728 (61 / 100) 163 (17 / (100 * 12728)) (26 / (10 * 12728)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12728 (61 / 100) 163 (17 / (100 * 12728)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (473410151 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (37194387 / 25000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5027225899 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12728 / 12728 * (61 / 100)) ^ 4 * inverseRadius8 (12728 - 1) /
            envelopeGap 12728 (61 / 100) 163 (17 / (100 * 12728)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12728

namespace BstLean.Part266.Row12728
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12728 163 ≤ (1139384377 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12728 163 ≤ (760235907 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (365446003 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12728 163 ≤ (1821126527 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12728 163 ≤ (647848399 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12728 163 ≤ (473415021 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (473410151 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (473410151 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (37194387 / 25000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5027225899 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1827319 / 500000000) : ℝ) ≤ √(17 / (100 * 12728) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12728) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2175799051 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3857169273 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12728) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12728) ≤ (111110431 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12728) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12728 * (163 : ℝ) ^ 2 + 26 / (10 * 12728) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12728) : ℝ)) (tA 12728 * 163 ^ 2 + 26 / (10 * 12728)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1827319 / 500000000))) * ((473410151 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1827319 / 500000000)) ^ 3) * ((37194387 / 25000000000000000000000))) + ((5027225899 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1827319 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12728) : ℝ)) d.D d.V d.P (√(tA 12728) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1827319 / 500000000)) ^ 2 * (((2175799051 / 1000000000000000)) * ((3857169273 / 100000000000000000)))) + ((5027225899 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12728) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1827319 / 500000000)) * ((473410151 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12728) : ℝ)) (tA 12728 * 163 ^ 2 + 26 / (10 * 12728)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((473410151 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1827319 / 500000000)) ^ 2) * ((37194387 / 25000000000000000000000)) + ((5027225899 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12728) : ℝ)) (√(26 / (10 * 12728) : ℝ)) d.D d.V d.P (√(tA 12728) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1827319 / 500000000)) * (((2175799051 / 1000000000000000)) * ((3857169273 / 100000000000000000))) + ((5027225899 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12728) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((473410151 / 100000000000000000000) : ℝ) + ((5027225899 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12728

namespace BstLean.Part266.Row12728
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12728 163 ∧
    0 ≤ (tableEnvelope C).f1 12728 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12728 163 ∧
    0 ≤ (tableEnvelope C).w1 12728 163 ∧ 0 ≤ (tableEnvelope C).w2 12728 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12728 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12728 163 ∧ 0 ≤ d.f1 12728 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12728 163 ∧ 0 ≤ d.w1 12728 163 ∧ 0 ≤ d.w2 12728 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12728 ≤ 2 * (228 / 100 : ℝ) / 12728 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12728 ≤ 2 * (370 / 100 : ℝ) / 12728 := by
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
    (completeRAData (tableEnvelope C) 12728 163).locationBound 12728 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12728 163).energyBound 12728 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12728 163) (d.f1 12728 163) d.f2 ≤
      32 * (((1139384377 / 250000000000000000) : ℝ) + (760235907 / 500000000000000000) + (365446003 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12728 163) (d.w1 12728 163)
      (d.w2 12728 163) ≤
      32 * (((1821126527 / 100000000000000000000) : ℝ) + (647848399 / 50000000000000000000) + (473415021 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12728 163) (d.f1 12728 163) d.f2 ≤
      ((1139384377 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1139384377 / 250000000000000000)) * ((760235907 / 500000000000000000)) * (126 / 100) +
      2 * (((760235907 / 500000000000000000)) ^ 2 + 2 * ((1139384377 / 250000000000000000)) * ((365446003 / 1000000000000000000))) +
      6 * ((760235907 / 500000000000000000)) * ((365446003 / 1000000000000000000)) * (126 / 100) + 8 * ((365446003 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12728 163) (d.f1 12728 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12728 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12728 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12728 163) (d.f1 12728 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12728 163) (d.w1 12728 163) (d.w2 12728 163)
  have hwexpr0 : 0 ≤ d.w0 12728 163 + d.w1 12728 163 * √(π / 2) +
      2 * d.w2 12728 163 + energyR16 12728 *
      radiusPolynomialRoot16 (d.w0 12728 163) (d.w1 12728 163) (d.w2 12728 163) := by
    positivity
  constructor
  · change (12728 : ℝ) ^ 8 * (mA 12728 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12728 163) (d.f1 12728 163) d.f2 + locationR16 12728 *
        radiusPolynomialRoot16 (d.f0 12728 163) (d.f1 12728 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12728 : ℝ) ^ 8 * (mA 12728 : ℝ) ^ 8 *
        ((((1139384377 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1139384377 / 250000000000000000)) * ((760235907 / 500000000000000000)) * (126 / 100) +
          2 * (((760235907 / 500000000000000000)) ^ 2 + 2 * ((1139384377 / 250000000000000000)) * ((365446003 / 1000000000000000000))) +
          6 * ((760235907 / 500000000000000000)) * ((365446003 / 1000000000000000000)) * (126 / 100) + 8 * ((365446003 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12728) *
          (32 * (((1139384377 / 250000000000000000) : ℝ) + (760235907 / 500000000000000000) + (365446003 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12728 : ℝ) ^ 16 *
      (d.w0 12728 163 + d.w1 12728 163 * √(π / 2) + 2 * d.w2 12728 163 +
        energyR16 12728 * radiusPolynomialRoot16 (d.w0 12728 163) (d.w1 12728 163)
          (d.w2 12728 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12728 : ℝ) ^ 16 *
        (((1821126527 / 100000000000000000000) : ℝ) + ((647848399 / 50000000000000000000)) * (126 / 100) + 2 * ((473415021 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12728) *
          (32 * (((1821126527 / 100000000000000000000) : ℝ) + (647848399 / 50000000000000000000) + (473415021 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12728

/-! A coarse bound on the actual paper statistics constant at dimension 12729. -/
namespace BstLean.Part266.Row12729
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12727 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12727 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12727 128 ≤ (12981 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12981 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12729) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12729 : ℕ))
    (by norm_num : (12729 : ℕ) ≤ 16384)
  have ht : paperTail256 12729 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12729 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12729 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12729 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12729 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12729 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12727 128 * √(2 / (12729 : ℝ)) *
      (√(12729 : ℝ) + paperT0 12729 + paperTail256 12729) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12729 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12729 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12729 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12727 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12727 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12729 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12729

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12729
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12729 (61 / 100) 163 (17 / (100 * 12729)) (26 / (10 * 12729)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12729 (61 / 100) 163 (17 / (100 * 12729)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (23664929 / 5000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (743653997 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1256009151 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12729 / 12729 * (61 / 100)) ^ 4 * inverseRadius8 (12729 - 1) /
            envelopeGap 12729 (61 / 100) 163 (17 / (100 * 12729)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12729

namespace BstLean.Part266.Row12729
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12729 163 ≤ (2278321993 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12729 163 ≤ (760086779 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (365374273 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12729 163 ≤ (1820697657 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12729 163 ≤ (1295391591 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12729 163 ≤ (473303447 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (23664929 / 5000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (23664929 / 5000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (743653997 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1256009151 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1827247 / 500000000) : ℝ) ≤ √(17 / (100 * 12729) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12729) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (435108529 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38565632291 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12729) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12729) ≤ (55550851 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12729) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12729 * (163 : ℝ) ^ 2 + 26 / (10 * 12729) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12729) : ℝ)) (tA 12729 * 163 ^ 2 + 26 / (10 * 12729)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1827247 / 500000000))) * ((23664929 / 5000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1827247 / 500000000)) ^ 3) * ((743653997 / 500000000000000000000000))) + ((1256009151 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1827247 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12729) : ℝ)) d.D d.V d.P (√(tA 12729) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1827247 / 500000000)) ^ 2 * (((435108529 / 200000000000000)) * ((38565632291 / 1000000000000000000)))) + ((1256009151 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12729) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1827247 / 500000000)) * ((23664929 / 5000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12729) : ℝ)) (tA 12729 * 163 ^ 2 + 26 / (10 * 12729)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((23664929 / 5000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1827247 / 500000000)) ^ 2) * ((743653997 / 500000000000000000000000)) + ((1256009151 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12729) : ℝ)) (√(26 / (10 * 12729) : ℝ)) d.D d.V d.P (√(tA 12729) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1827247 / 500000000)) * (((435108529 / 200000000000000)) * ((38565632291 / 1000000000000000000))) + ((1256009151 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12729) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((23664929 / 5000000000000000000) : ℝ) + ((1256009151 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12729

namespace BstLean.Part266.Row12729
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12729 163 ∧
    0 ≤ (tableEnvelope C).f1 12729 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12729 163 ∧
    0 ≤ (tableEnvelope C).w1 12729 163 ∧ 0 ≤ (tableEnvelope C).w2 12729 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12729 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12729 163 ∧ 0 ≤ d.f1 12729 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12729 163 ∧ 0 ≤ d.w1 12729 163 ∧ 0 ≤ d.w2 12729 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12729 ≤ 2 * (228 / 100 : ℝ) / 12729 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12729 ≤ 2 * (370 / 100 : ℝ) / 12729 := by
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
    (completeRAData (tableEnvelope C) 12729 163).locationBound 12729 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12729 163).energyBound 12729 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12729 163) (d.f1 12729 163) d.f2 ≤
      32 * (((2278321993 / 500000000000000000) : ℝ) + (760086779 / 500000000000000000) + (365374273 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12729 163) (d.w1 12729 163)
      (d.w2 12729 163) ≤
      32 * (((1820697657 / 100000000000000000000) : ℝ) + (1295391591 / 100000000000000000000) + (473303447 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12729 163) (d.f1 12729 163) d.f2 ≤
      ((2278321993 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2278321993 / 500000000000000000)) * ((760086779 / 500000000000000000)) * (126 / 100) +
      2 * (((760086779 / 500000000000000000)) ^ 2 + 2 * ((2278321993 / 500000000000000000)) * ((365374273 / 1000000000000000000))) +
      6 * ((760086779 / 500000000000000000)) * ((365374273 / 1000000000000000000)) * (126 / 100) + 8 * ((365374273 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12729 163) (d.f1 12729 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12729 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12729 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12729 163) (d.f1 12729 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12729 163) (d.w1 12729 163) (d.w2 12729 163)
  have hwexpr0 : 0 ≤ d.w0 12729 163 + d.w1 12729 163 * √(π / 2) +
      2 * d.w2 12729 163 + energyR16 12729 *
      radiusPolynomialRoot16 (d.w0 12729 163) (d.w1 12729 163) (d.w2 12729 163) := by
    positivity
  constructor
  · change (12729 : ℝ) ^ 8 * (mA 12729 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12729 163) (d.f1 12729 163) d.f2 + locationR16 12729 *
        radiusPolynomialRoot16 (d.f0 12729 163) (d.f1 12729 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12729 : ℝ) ^ 8 * (mA 12729 : ℝ) ^ 8 *
        ((((2278321993 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2278321993 / 500000000000000000)) * ((760086779 / 500000000000000000)) * (126 / 100) +
          2 * (((760086779 / 500000000000000000)) ^ 2 + 2 * ((2278321993 / 500000000000000000)) * ((365374273 / 1000000000000000000))) +
          6 * ((760086779 / 500000000000000000)) * ((365374273 / 1000000000000000000)) * (126 / 100) + 8 * ((365374273 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12729) *
          (32 * (((2278321993 / 500000000000000000) : ℝ) + (760086779 / 500000000000000000) + (365374273 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12729 : ℝ) ^ 16 *
      (d.w0 12729 163 + d.w1 12729 163 * √(π / 2) + 2 * d.w2 12729 163 +
        energyR16 12729 * radiusPolynomialRoot16 (d.w0 12729 163) (d.w1 12729 163)
          (d.w2 12729 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12729 : ℝ) ^ 16 *
        (((1820697657 / 100000000000000000000) : ℝ) + ((1295391591 / 100000000000000000000)) * (126 / 100) + 2 * ((473303447 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12729) *
          (32 * (((1820697657 / 100000000000000000000) : ℝ) + (1295391591 / 100000000000000000000) + (473303447 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12729

/-! A coarse bound on the actual paper statistics constant at dimension 12730. -/
namespace BstLean.Part266.Row12730
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12728 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12728 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12728 128 ≤ (12982 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12982 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12730) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12730 : ℕ))
    (by norm_num : (12730 : ℕ) ≤ 16384)
  have ht : paperTail256 12730 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12730 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12730 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12730 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12730 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12730 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12728 128 * √(2 / (12730 : ℝ)) *
      (√(12730 : ℝ) + paperT0 12730 + paperTail256 12730) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12730 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12730 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12730 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12728 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12728 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12730 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12730

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12730
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12730 (61 / 100) 163 (17 / (100 * 12730)) (26 / (10 * 12730)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12730 (61 / 100) 163 (17 / (100 * 12730)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (473187043 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1486840691 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5020849587 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12730 / 12730 * (61 / 100)) ^ 4 * inverseRadius8 (12730 - 1) /
            envelopeGap 12730 (61 / 100) 163 (17 / (100 * 12730)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12730

namespace BstLean.Part266.Row12730
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12730 163 ≤ (284734423 / 62500000000000000)
  f1 : (tableEnvelope C).f1 12730 163 ≤ (303975079 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (365302563 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12730 163 ≤ (455067233 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12730 163 ≤ (1295086483 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12730 163 ≤ (473191907 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (473187043 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (473187043 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1486840691 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5020849587 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((73087 / 20000000) : ℝ) ≤ √(17 / (100 * 12730) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12730) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2175286287 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19279786637 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12730) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12730) ≤ (4443719 / 40000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12730) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12730 * (163 : ℝ) ^ 2 + 26 / (10 * 12730) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12730) : ℝ)) (tA 12730 * 163 ^ 2 + 26 / (10 * 12730)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((73087 / 20000000))) * ((473187043 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((73087 / 20000000)) ^ 3) * ((1486840691 / 1000000000000000000000000))) + ((5020849587 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((73087 / 20000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12730) : ℝ)) d.D d.V d.P (√(tA 12730) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((73087 / 20000000)) ^ 2 * (((2175286287 / 1000000000000000)) * ((19279786637 / 500000000000000000)))) + ((5020849587 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12730) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((73087 / 20000000)) * ((473187043 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12730) : ℝ)) (tA 12730 * 163 ^ 2 + 26 / (10 * 12730)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((473187043 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((73087 / 20000000)) ^ 2) * ((1486840691 / 1000000000000000000000000)) + ((5020849587 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12730) : ℝ)) (√(26 / (10 * 12730) : ℝ)) d.D d.V d.P (√(tA 12730) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((73087 / 20000000)) * (((2175286287 / 1000000000000000)) * ((19279786637 / 500000000000000000))) + ((5020849587 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12730) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((473187043 / 100000000000000000000) : ℝ) + ((5020849587 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12730

namespace BstLean.Part266.Row12730
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12730 163 ∧
    0 ≤ (tableEnvelope C).f1 12730 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12730 163 ∧
    0 ≤ (tableEnvelope C).w1 12730 163 ∧ 0 ≤ (tableEnvelope C).w2 12730 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12730 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12730 163 ∧ 0 ≤ d.f1 12730 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12730 163 ∧ 0 ≤ d.w1 12730 163 ∧ 0 ≤ d.w2 12730 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12730 ≤ 2 * (228 / 100 : ℝ) / 12730 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12730 ≤ 2 * (370 / 100 : ℝ) / 12730 := by
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
    (completeRAData (tableEnvelope C) 12730 163).locationBound 12730 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12730 163).energyBound 12730 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12730 163) (d.f1 12730 163) d.f2 ≤
      32 * (((284734423 / 62500000000000000) : ℝ) + (303975079 / 200000000000000000) + (365302563 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12730 163) (d.w1 12730 163)
      (d.w2 12730 163) ≤
      32 * (((455067233 / 25000000000000000000) : ℝ) + (1295086483 / 100000000000000000000) + (473191907 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12730 163) (d.f1 12730 163) d.f2 ≤
      ((284734423 / 62500000000000000) : ℝ) ^ 2 + 2 * ((284734423 / 62500000000000000)) * ((303975079 / 200000000000000000)) * (126 / 100) +
      2 * (((303975079 / 200000000000000000)) ^ 2 + 2 * ((284734423 / 62500000000000000)) * ((365302563 / 1000000000000000000))) +
      6 * ((303975079 / 200000000000000000)) * ((365302563 / 1000000000000000000)) * (126 / 100) + 8 * ((365302563 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12730 163) (d.f1 12730 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12730 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12730 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12730 163) (d.f1 12730 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12730 163) (d.w1 12730 163) (d.w2 12730 163)
  have hwexpr0 : 0 ≤ d.w0 12730 163 + d.w1 12730 163 * √(π / 2) +
      2 * d.w2 12730 163 + energyR16 12730 *
      radiusPolynomialRoot16 (d.w0 12730 163) (d.w1 12730 163) (d.w2 12730 163) := by
    positivity
  constructor
  · change (12730 : ℝ) ^ 8 * (mA 12730 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12730 163) (d.f1 12730 163) d.f2 + locationR16 12730 *
        radiusPolynomialRoot16 (d.f0 12730 163) (d.f1 12730 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12730 : ℝ) ^ 8 * (mA 12730 : ℝ) ^ 8 *
        ((((284734423 / 62500000000000000) : ℝ) ^ 2 + 2 * ((284734423 / 62500000000000000)) * ((303975079 / 200000000000000000)) * (126 / 100) +
          2 * (((303975079 / 200000000000000000)) ^ 2 + 2 * ((284734423 / 62500000000000000)) * ((365302563 / 1000000000000000000))) +
          6 * ((303975079 / 200000000000000000)) * ((365302563 / 1000000000000000000)) * (126 / 100) + 8 * ((365302563 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12730) *
          (32 * (((284734423 / 62500000000000000) : ℝ) + (303975079 / 200000000000000000) + (365302563 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12730 : ℝ) ^ 16 *
      (d.w0 12730 163 + d.w1 12730 163 * √(π / 2) + 2 * d.w2 12730 163 +
        energyR16 12730 * radiusPolynomialRoot16 (d.w0 12730 163) (d.w1 12730 163)
          (d.w2 12730 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12730 : ℝ) ^ 16 *
        (((455067233 / 25000000000000000000) : ℝ) + ((1295086483 / 100000000000000000000)) * (126 / 100) + 2 * ((473191907 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12730) *
          (32 * (((455067233 / 25000000000000000000) : ℝ) + (1295086483 / 100000000000000000000) + (473191907 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12730

/-! A coarse bound on the actual paper statistics constant at dimension 12731. -/
namespace BstLean.Part266.Row12731
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12729 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12729 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12729 128 ≤ (12983 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12983 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12731) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12731 : ℕ))
    (by norm_num : (12731 : ℕ) ≤ 16384)
  have ht : paperTail256 12731 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12731 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12731 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12731 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12731 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12731 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12729 128 * √(2 / (12731 : ℝ)) *
      (√(12731 : ℝ) + paperT0 12731 + paperTail256 12731) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12731 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12731 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12731 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12729 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12729 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12731 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12731

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12731
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12731 (61 / 100) 163 (17 / (100 * 12731)) (26 / (10 * 12731)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12731 (61 / 100) 163 (17 / (100 * 12731)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (236537771 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (371593393 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5017664847 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12731 / 12731 * (61 / 100)) ^ 4 * inverseRadius8 (12731 - 1) /
            envelopeGap 12731 (61 / 100) 163 (17 / (100 * 12731)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12731

namespace BstLean.Part266.Row12731
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12731 163 ≤ (4554854261 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12731 163 ≤ (1519576499 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (45653847 / 125000000000000000)
  w0 : (tableEnvelope C).w0 12731 163 ≤ (1819839619 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12731 163 ≤ (10358249 / 800000000000000000)
  w2 : (tableEnvelope C).w2 12731 163 ≤ (473080403 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (236537771 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (236537771 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (371593393 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5017664847 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3654207 / 1000000000) : ℝ) ≤ √(17 / (100 * 12731) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12731) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1087514991 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3855351569 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12731) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12731) ≤ (111084249 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12731) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12731 * (163 : ℝ) ^ 2 + 26 / (10 * 12731) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12731) : ℝ)) (tA 12731 * 163 ^ 2 + 26 / (10 * 12731)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3654207 / 1000000000))) * ((236537771 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3654207 / 1000000000)) ^ 3) * ((371593393 / 250000000000000000000000))) + ((5017664847 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3654207 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12731) : ℝ)) d.D d.V d.P (√(tA 12731) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3654207 / 1000000000)) ^ 2 * (((1087514991 / 500000000000000)) * ((3855351569 / 100000000000000000)))) + ((5017664847 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12731) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3654207 / 1000000000)) * ((236537771 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12731) : ℝ)) (tA 12731 * 163 ^ 2 + 26 / (10 * 12731)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((236537771 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3654207 / 1000000000)) ^ 2) * ((371593393 / 250000000000000000000000)) + ((5017664847 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12731) : ℝ)) (√(26 / (10 * 12731) : ℝ)) d.D d.V d.P (√(tA 12731) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3654207 / 1000000000)) * (((1087514991 / 500000000000000)) * ((3855351569 / 100000000000000000))) + ((5017664847 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12731) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((236537771 / 50000000000000000000) : ℝ) + ((5017664847 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12731

namespace BstLean.Part266.Row12731
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12731 163 ∧
    0 ≤ (tableEnvelope C).f1 12731 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12731 163 ∧
    0 ≤ (tableEnvelope C).w1 12731 163 ∧ 0 ≤ (tableEnvelope C).w2 12731 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12731 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12731 163 ∧ 0 ≤ d.f1 12731 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12731 163 ∧ 0 ≤ d.w1 12731 163 ∧ 0 ≤ d.w2 12731 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12731 ≤ 2 * (228 / 100 : ℝ) / 12731 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12731 ≤ 2 * (370 / 100 : ℝ) / 12731 := by
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
    (completeRAData (tableEnvelope C) 12731 163).locationBound 12731 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12731 163).energyBound 12731 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12731 163) (d.f1 12731 163) d.f2 ≤
      32 * (((4554854261 / 1000000000000000000) : ℝ) + (1519576499 / 1000000000000000000) + (45653847 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12731 163) (d.w1 12731 163)
      (d.w2 12731 163) ≤
      32 * (((1819839619 / 100000000000000000000) : ℝ) + (10358249 / 800000000000000000) + (473080403 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12731 163) (d.f1 12731 163) d.f2 ≤
      ((4554854261 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4554854261 / 1000000000000000000)) * ((1519576499 / 1000000000000000000)) * (126 / 100) +
      2 * (((1519576499 / 1000000000000000000)) ^ 2 + 2 * ((4554854261 / 1000000000000000000)) * ((45653847 / 125000000000000000))) +
      6 * ((1519576499 / 1000000000000000000)) * ((45653847 / 125000000000000000)) * (126 / 100) + 8 * ((45653847 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12731 163) (d.f1 12731 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12731 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12731 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12731 163) (d.f1 12731 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12731 163) (d.w1 12731 163) (d.w2 12731 163)
  have hwexpr0 : 0 ≤ d.w0 12731 163 + d.w1 12731 163 * √(π / 2) +
      2 * d.w2 12731 163 + energyR16 12731 *
      radiusPolynomialRoot16 (d.w0 12731 163) (d.w1 12731 163) (d.w2 12731 163) := by
    positivity
  constructor
  · change (12731 : ℝ) ^ 8 * (mA 12731 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12731 163) (d.f1 12731 163) d.f2 + locationR16 12731 *
        radiusPolynomialRoot16 (d.f0 12731 163) (d.f1 12731 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12731 : ℝ) ^ 8 * (mA 12731 : ℝ) ^ 8 *
        ((((4554854261 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4554854261 / 1000000000000000000)) * ((1519576499 / 1000000000000000000)) * (126 / 100) +
          2 * (((1519576499 / 1000000000000000000)) ^ 2 + 2 * ((4554854261 / 1000000000000000000)) * ((45653847 / 125000000000000000))) +
          6 * ((1519576499 / 1000000000000000000)) * ((45653847 / 125000000000000000)) * (126 / 100) + 8 * ((45653847 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12731) *
          (32 * (((4554854261 / 1000000000000000000) : ℝ) + (1519576499 / 1000000000000000000) + (45653847 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12731 : ℝ) ^ 16 *
      (d.w0 12731 163 + d.w1 12731 163 * √(π / 2) + 2 * d.w2 12731 163 +
        energyR16 12731 * radiusPolynomialRoot16 (d.w0 12731 163) (d.w1 12731 163)
          (d.w2 12731 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12731 : ℝ) ^ 16 *
        (((1819839619 / 100000000000000000000) : ℝ) + ((10358249 / 800000000000000000)) * (126 / 100) + 2 * ((473080403 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12731) *
          (32 * (((1819839619 / 100000000000000000000) : ℝ) + (10358249 / 800000000000000000) + (473080403 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12731

/-! A coarse bound on the actual paper statistics constant at dimension 12732. -/
namespace BstLean.Part266.Row12732
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12730 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12730 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12730 128 ≤ (12984 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12984 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12732) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12732 : ℕ))
    (by norm_num : (12732 : ℕ) ≤ 16384)
  have ht : paperTail256 12732 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12732 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12732 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12732 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12732 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12732 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12730 128 * √(2 / (12732 : ℝ)) *
      (√(12732 : ℝ) + paperT0 12732 + paperTail256 12732) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12732 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12732 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12732 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12730 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12730 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12732 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12732

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12732
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12732 (61 / 100) 163 (17 / (100 * 12732)) (26 / (10 * 12732)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12732 (61 / 100) 163 (17 / (100 * 12732)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (18918563 / 4000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (371476659 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2507241191 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12732 / 12732 * (61 / 100)) ^ 4 * inverseRadius8 (12732 - 1) /
            envelopeGap 12732 (61 / 100) 163 (17 / (100 * 12732)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12732

namespace BstLean.Part266.Row12732
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12732 163 ≤ (569245207 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12732 163 ≤ (23738727 / 15625000000000000)
  f2 : (tableEnvelope C).f2 ≤ (365159109 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12732 163 ≤ (1819411189 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12732 163 ≤ (1294476221 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12732 163 ≤ (472968933 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (18918563 / 4000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (18918563 / 4000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (371476659 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2507241191 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3654063 / 1000000000) : ℝ) ≤ √(17 / (100 * 12732) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12732) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (543693431 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4818432441 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12732) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12732) ≤ (27768881 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12732) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12732 * (163 : ℝ) ^ 2 + 26 / (10 * 12732) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12732) : ℝ)) (tA 12732 * 163 ^ 2 + 26 / (10 * 12732)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3654063 / 1000000000))) * ((18918563 / 4000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3654063 / 1000000000)) ^ 3) * ((371476659 / 250000000000000000000000))) + ((2507241191 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3654063 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12732) : ℝ)) d.D d.V d.P (√(tA 12732) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3654063 / 1000000000)) ^ 2 * (((543693431 / 250000000000000)) * ((4818432441 / 125000000000000000)))) + ((2507241191 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12732) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3654063 / 1000000000)) * ((18918563 / 4000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12732) : ℝ)) (tA 12732 * 163 ^ 2 + 26 / (10 * 12732)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((18918563 / 4000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3654063 / 1000000000)) ^ 2) * ((371476659 / 250000000000000000000000)) + ((2507241191 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12732) : ℝ)) (√(26 / (10 * 12732) : ℝ)) d.D d.V d.P (√(tA 12732) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3654063 / 1000000000)) * (((543693431 / 250000000000000)) * ((4818432441 / 125000000000000000))) + ((2507241191 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12732) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((18918563 / 4000000000000000000) : ℝ) + ((2507241191 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12732

namespace BstLean.Part266.Row12732
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12732 163 ∧
    0 ≤ (tableEnvelope C).f1 12732 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12732 163 ∧
    0 ≤ (tableEnvelope C).w1 12732 163 ∧ 0 ≤ (tableEnvelope C).w2 12732 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12732 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12732 163 ∧ 0 ≤ d.f1 12732 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12732 163 ∧ 0 ≤ d.w1 12732 163 ∧ 0 ≤ d.w2 12732 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12732 ≤ 2 * (228 / 100 : ℝ) / 12732 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12732 ≤ 2 * (370 / 100 : ℝ) / 12732 := by
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
    (completeRAData (tableEnvelope C) 12732 163).locationBound 12732 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12732 163).energyBound 12732 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12732 163) (d.f1 12732 163) d.f2 ≤
      32 * (((569245207 / 125000000000000000) : ℝ) + (23738727 / 15625000000000000) + (365159109 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12732 163) (d.w1 12732 163)
      (d.w2 12732 163) ≤
      32 * (((1819411189 / 100000000000000000000) : ℝ) + (1294476221 / 100000000000000000000) + (472968933 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12732 163) (d.f1 12732 163) d.f2 ≤
      ((569245207 / 125000000000000000) : ℝ) ^ 2 + 2 * ((569245207 / 125000000000000000)) * ((23738727 / 15625000000000000)) * (126 / 100) +
      2 * (((23738727 / 15625000000000000)) ^ 2 + 2 * ((569245207 / 125000000000000000)) * ((365159109 / 1000000000000000000))) +
      6 * ((23738727 / 15625000000000000)) * ((365159109 / 1000000000000000000)) * (126 / 100) + 8 * ((365159109 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12732 163) (d.f1 12732 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12732 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12732 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12732 163) (d.f1 12732 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12732 163) (d.w1 12732 163) (d.w2 12732 163)
  have hwexpr0 : 0 ≤ d.w0 12732 163 + d.w1 12732 163 * √(π / 2) +
      2 * d.w2 12732 163 + energyR16 12732 *
      radiusPolynomialRoot16 (d.w0 12732 163) (d.w1 12732 163) (d.w2 12732 163) := by
    positivity
  constructor
  · change (12732 : ℝ) ^ 8 * (mA 12732 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12732 163) (d.f1 12732 163) d.f2 + locationR16 12732 *
        radiusPolynomialRoot16 (d.f0 12732 163) (d.f1 12732 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12732 : ℝ) ^ 8 * (mA 12732 : ℝ) ^ 8 *
        ((((569245207 / 125000000000000000) : ℝ) ^ 2 + 2 * ((569245207 / 125000000000000000)) * ((23738727 / 15625000000000000)) * (126 / 100) +
          2 * (((23738727 / 15625000000000000)) ^ 2 + 2 * ((569245207 / 125000000000000000)) * ((365159109 / 1000000000000000000))) +
          6 * ((23738727 / 15625000000000000)) * ((365159109 / 1000000000000000000)) * (126 / 100) + 8 * ((365159109 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12732) *
          (32 * (((569245207 / 125000000000000000) : ℝ) + (23738727 / 15625000000000000) + (365159109 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12732 : ℝ) ^ 16 *
      (d.w0 12732 163 + d.w1 12732 163 * √(π / 2) + 2 * d.w2 12732 163 +
        energyR16 12732 * radiusPolynomialRoot16 (d.w0 12732 163) (d.w1 12732 163)
          (d.w2 12732 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12732 : ℝ) ^ 16 *
        (((1819411189 / 100000000000000000000) : ℝ) + ((1294476221 / 100000000000000000000)) * (126 / 100) + 2 * ((472968933 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12732) *
          (32 * (((1819411189 / 100000000000000000000) : ℝ) + (1294476221 / 100000000000000000000) + (472968933 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12732

/-! A coarse bound on the actual paper statistics constant at dimension 12733. -/
namespace BstLean.Part266.Row12733
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12731 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12731 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12731 128 ≤ (12985 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12985 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12733) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12733 : ℕ))
    (by norm_num : (12733 : ℕ) ≤ 16384)
  have ht : paperTail256 12733 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12733 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12733 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12733 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12733 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12733 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12731 128 * √(2 / (12733 : ℝ)) *
      (√(12733 : ℝ) + paperT0 12733 + paperTail256 12733) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12733 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12733 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12733 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12731 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12731 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12733 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12733

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12733
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12733 (61 / 100) 163 (17 / (100 * 12733)) (26 / (10 * 12733)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12733 (61 / 100) 163 (17 / (100 * 12733)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (118213161 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1485439883 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (501130219 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12733 / 12733 * (61 / 100)) ^ 4 * inverseRadius8 (12733 - 1) /
            envelopeGap 12733 (61 / 100) 163 (17 / (100 * 12733)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12733

namespace BstLean.Part266.Row12733
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12733 163 ≤ (28456661 / 6250000000000000)
  f1 : (tableEnvelope C).f1 12733 163 ≤ (94936239 / 62500000000000000)
  f2 : (tableEnvelope C).f2 ≤ (73017473 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12733 163 ≤ (181898217 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 12733 163 ≤ (258834213 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12733 163 ≤ (472857499 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (118213161 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (118213161 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1485439883 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (501130219 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((22837 / 6250000) : ℝ) ≤ √(17 / (100 * 12733) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12733) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2174517519 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9635351197 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12733) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12733) ≤ (277667 / 2500000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12733) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12733 * (163 : ℝ) ^ 2 + 26 / (10 * 12733) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12733) : ℝ)) (tA 12733 * 163 ^ 2 + 26 / (10 * 12733)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((22837 / 6250000))) * ((118213161 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((22837 / 6250000)) ^ 3) * ((1485439883 / 1000000000000000000000000))) + ((501130219 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((22837 / 6250000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12733) : ℝ)) d.D d.V d.P (√(tA 12733) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((22837 / 6250000)) ^ 2 * (((2174517519 / 1000000000000000)) * ((9635351197 / 250000000000000000)))) + ((501130219 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12733) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((22837 / 6250000)) * ((118213161 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12733) : ℝ)) (tA 12733 * 163 ^ 2 + 26 / (10 * 12733)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((118213161 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((22837 / 6250000)) ^ 2) * ((1485439883 / 1000000000000000000000000)) + ((501130219 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12733) : ℝ)) (√(26 / (10 * 12733) : ℝ)) d.D d.V d.P (√(tA 12733) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((22837 / 6250000)) * (((2174517519 / 1000000000000000)) * ((9635351197 / 250000000000000000))) + ((501130219 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12733) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((118213161 / 25000000000000000000) : ℝ) + ((501130219 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12733

namespace BstLean.Part266.Row12733
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12733 163 ∧
    0 ≤ (tableEnvelope C).f1 12733 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12733 163 ∧
    0 ≤ (tableEnvelope C).w1 12733 163 ∧ 0 ≤ (tableEnvelope C).w2 12733 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12733 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12733 163 ∧ 0 ≤ d.f1 12733 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12733 163 ∧ 0 ≤ d.w1 12733 163 ∧ 0 ≤ d.w2 12733 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12733 ≤ 2 * (228 / 100 : ℝ) / 12733 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12733 ≤ 2 * (370 / 100 : ℝ) / 12733 := by
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
    (completeRAData (tableEnvelope C) 12733 163).locationBound 12733 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12733 163).energyBound 12733 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12733 163) (d.f1 12733 163) d.f2 ≤
      32 * (((28456661 / 6250000000000000) : ℝ) + (94936239 / 62500000000000000) + (73017473 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12733 163) (d.w1 12733 163)
      (d.w2 12733 163) ≤
      32 * (((181898217 / 10000000000000000000) : ℝ) + (258834213 / 20000000000000000000) + (472857499 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12733 163) (d.f1 12733 163) d.f2 ≤
      ((28456661 / 6250000000000000) : ℝ) ^ 2 + 2 * ((28456661 / 6250000000000000)) * ((94936239 / 62500000000000000)) * (126 / 100) +
      2 * (((94936239 / 62500000000000000)) ^ 2 + 2 * ((28456661 / 6250000000000000)) * ((73017473 / 200000000000000000))) +
      6 * ((94936239 / 62500000000000000)) * ((73017473 / 200000000000000000)) * (126 / 100) + 8 * ((73017473 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12733 163) (d.f1 12733 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12733 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12733 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12733 163) (d.f1 12733 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12733 163) (d.w1 12733 163) (d.w2 12733 163)
  have hwexpr0 : 0 ≤ d.w0 12733 163 + d.w1 12733 163 * √(π / 2) +
      2 * d.w2 12733 163 + energyR16 12733 *
      radiusPolynomialRoot16 (d.w0 12733 163) (d.w1 12733 163) (d.w2 12733 163) := by
    positivity
  constructor
  · change (12733 : ℝ) ^ 8 * (mA 12733 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12733 163) (d.f1 12733 163) d.f2 + locationR16 12733 *
        radiusPolynomialRoot16 (d.f0 12733 163) (d.f1 12733 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12733 : ℝ) ^ 8 * (mA 12733 : ℝ) ^ 8 *
        ((((28456661 / 6250000000000000) : ℝ) ^ 2 + 2 * ((28456661 / 6250000000000000)) * ((94936239 / 62500000000000000)) * (126 / 100) +
          2 * (((94936239 / 62500000000000000)) ^ 2 + 2 * ((28456661 / 6250000000000000)) * ((73017473 / 200000000000000000))) +
          6 * ((94936239 / 62500000000000000)) * ((73017473 / 200000000000000000)) * (126 / 100) + 8 * ((73017473 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12733) *
          (32 * (((28456661 / 6250000000000000) : ℝ) + (94936239 / 62500000000000000) + (73017473 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12733 : ℝ) ^ 16 *
      (d.w0 12733 163 + d.w1 12733 163 * √(π / 2) + 2 * d.w2 12733 163 +
        energyR16 12733 * radiusPolynomialRoot16 (d.w0 12733 163) (d.w1 12733 163)
          (d.w2 12733 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12733 : ℝ) ^ 16 *
        (((181898217 / 10000000000000000000) : ℝ) + ((258834213 / 20000000000000000000)) * (126 / 100) + 2 * ((472857499 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12733) *
          (32 * (((181898217 / 10000000000000000000) : ℝ) + (258834213 / 20000000000000000000) + (472857499 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12733

/-! A coarse bound on the actual paper statistics constant at dimension 12734. -/
namespace BstLean.Part266.Row12734
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12732 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12732 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12732 128 ≤ (12986 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12986 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12734) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12734 : ℕ))
    (by norm_num : (12734 : ℕ) ≤ 16384)
  have ht : paperTail256 12734 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12734 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12734 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12734 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12734 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12734 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12732 128 * √(2 / (12734 : ℝ)) *
      (√(12734 : ℝ) + paperT0 12734 + paperTail256 12734) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12734 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12734 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12734 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12732 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12732 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12734 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12734

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12734
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12734 (61 / 100) 163 (17 / (100 * 12734)) (26 / (10 * 12734)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12734 (61 / 100) 163 (17 / (100 * 12734)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (3693291 / 781250000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (742486657 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1252031067 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12734 / 12734 * (61 / 100)) ^ 4 * inverseRadius8 (12734 - 1) /
            envelopeGap 12734 (61 / 100) 163 (17 / (100 * 12734)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12734

namespace BstLean.Part266.Row12734
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12734 163 ≤ (2276085087 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12734 163 ≤ (11864697 / 7812500000000000)
  f2 : (tableEnvelope C).f2 ≤ (182507821 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12734 163 ≤ (1818553299 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12734 163 ≤ (1293866013 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12734 163 ≤ (4727461 / 1000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (3693291 / 781250000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (3693291 / 781250000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (742486657 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1252031067 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3653777 / 1000000000) : ℝ) ≤ √(17 / (100 * 12734) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12734) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (434852273 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7707070297 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12734) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12734) ≤ (55529039 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12734) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12734 * (163 : ℝ) ^ 2 + 26 / (10 * 12734) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12734) : ℝ)) (tA 12734 * 163 ^ 2 + 26 / (10 * 12734)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3653777 / 1000000000))) * ((3693291 / 781250000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3653777 / 1000000000)) ^ 3) * ((742486657 / 500000000000000000000000))) + ((1252031067 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3653777 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12734) : ℝ)) d.D d.V d.P (√(tA 12734) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3653777 / 1000000000)) ^ 2 * (((434852273 / 200000000000000)) * ((7707070297 / 200000000000000000)))) + ((1252031067 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12734) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3653777 / 1000000000)) * ((3693291 / 781250000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12734) : ℝ)) (tA 12734 * 163 ^ 2 + 26 / (10 * 12734)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((3693291 / 781250000000000000) : ℝ) + (24198 / 100000) / (2 * ((3653777 / 1000000000)) ^ 2) * ((742486657 / 500000000000000000000000)) + ((1252031067 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12734) : ℝ)) (√(26 / (10 * 12734) : ℝ)) d.D d.V d.P (√(tA 12734) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3653777 / 1000000000)) * (((434852273 / 200000000000000)) * ((7707070297 / 200000000000000000))) + ((1252031067 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12734) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((3693291 / 781250000000000000) : ℝ) + ((1252031067 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12734

namespace BstLean.Part266.Row12734
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12734 163 ∧
    0 ≤ (tableEnvelope C).f1 12734 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12734 163 ∧
    0 ≤ (tableEnvelope C).w1 12734 163 ∧ 0 ≤ (tableEnvelope C).w2 12734 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12734 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12734 163 ∧ 0 ≤ d.f1 12734 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12734 163 ∧ 0 ≤ d.w1 12734 163 ∧ 0 ≤ d.w2 12734 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12734 ≤ 2 * (228 / 100 : ℝ) / 12734 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12734 ≤ 2 * (370 / 100 : ℝ) / 12734 := by
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
    (completeRAData (tableEnvelope C) 12734 163).locationBound 12734 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12734 163).energyBound 12734 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12734 163) (d.f1 12734 163) d.f2 ≤
      32 * (((2276085087 / 500000000000000000) : ℝ) + (11864697 / 7812500000000000) + (182507821 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12734 163) (d.w1 12734 163)
      (d.w2 12734 163) ≤
      32 * (((1818553299 / 100000000000000000000) : ℝ) + (1293866013 / 100000000000000000000) + (4727461 / 1000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12734 163) (d.f1 12734 163) d.f2 ≤
      ((2276085087 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2276085087 / 500000000000000000)) * ((11864697 / 7812500000000000)) * (126 / 100) +
      2 * (((11864697 / 7812500000000000)) ^ 2 + 2 * ((2276085087 / 500000000000000000)) * ((182507821 / 500000000000000000))) +
      6 * ((11864697 / 7812500000000000)) * ((182507821 / 500000000000000000)) * (126 / 100) + 8 * ((182507821 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12734 163) (d.f1 12734 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12734 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12734 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12734 163) (d.f1 12734 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12734 163) (d.w1 12734 163) (d.w2 12734 163)
  have hwexpr0 : 0 ≤ d.w0 12734 163 + d.w1 12734 163 * √(π / 2) +
      2 * d.w2 12734 163 + energyR16 12734 *
      radiusPolynomialRoot16 (d.w0 12734 163) (d.w1 12734 163) (d.w2 12734 163) := by
    positivity
  constructor
  · change (12734 : ℝ) ^ 8 * (mA 12734 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12734 163) (d.f1 12734 163) d.f2 + locationR16 12734 *
        radiusPolynomialRoot16 (d.f0 12734 163) (d.f1 12734 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12734 : ℝ) ^ 8 * (mA 12734 : ℝ) ^ 8 *
        ((((2276085087 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2276085087 / 500000000000000000)) * ((11864697 / 7812500000000000)) * (126 / 100) +
          2 * (((11864697 / 7812500000000000)) ^ 2 + 2 * ((2276085087 / 500000000000000000)) * ((182507821 / 500000000000000000))) +
          6 * ((11864697 / 7812500000000000)) * ((182507821 / 500000000000000000)) * (126 / 100) + 8 * ((182507821 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12734) *
          (32 * (((2276085087 / 500000000000000000) : ℝ) + (11864697 / 7812500000000000) + (182507821 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12734 : ℝ) ^ 16 *
      (d.w0 12734 163 + d.w1 12734 163 * √(π / 2) + 2 * d.w2 12734 163 +
        energyR16 12734 * radiusPolynomialRoot16 (d.w0 12734 163) (d.w1 12734 163)
          (d.w2 12734 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12734 : ℝ) ^ 16 *
        (((1818553299 / 100000000000000000000) : ℝ) + ((1293866013 / 100000000000000000000)) * (126 / 100) + 2 * ((4727461 / 1000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12734) *
          (32 * (((1818553299 / 100000000000000000000) : ℝ) + (1293866013 / 100000000000000000000) + (4727461 / 1000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12734

/-! A coarse bound on the actual paper statistics constant at dimension 12735. -/
namespace BstLean.Part266.Row12735
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12733 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12733 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12733 128 ≤ (12987 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12987 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12735) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12735 : ℕ))
    (by norm_num : (12735 : ℕ) ≤ 16384)
  have ht : paperTail256 12735 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12735 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12735 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12735 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12735 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12735 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12733 128 * √(2 / (12735 : ℝ)) *
      (√(12735 : ℝ) + paperT0 12735 + paperTail256 12735) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12735 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12735 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12735 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12733 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12733 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12735 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12735

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12735
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12735 (61 / 100) 163 (17 / (100 * 12735)) (26 / (10 * 12735)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12735 (61 / 100) 163 (17 / (100 * 12735)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (236314943 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (92781683 / 62500000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5004948617 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12735 / 12735 * (61 / 100)) ^ 4 * inverseRadius8 (12735 - 1) /
            envelopeGap 12735 (61 / 100) 163 (17 / (100 * 12735)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12735

namespace BstLean.Part266.Row12735
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12735 163 ≤ (4551278489 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12735 163 ≤ (1518383533 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (364944039 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12735 163 ≤ (181812531 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 12735 163 ≤ (646780707 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12735 163 ≤ (94526947 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (236314943 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (236314943 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (92781683 / 62500000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5004948617 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3653633 / 1000000000) : ℝ) ≤ √(17 / (100 * 12735) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12735) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1087002629 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7705859921 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12735) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12735) ≤ (55524679 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12735) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12735 * (163 : ℝ) ^ 2 + 26 / (10 * 12735) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12735) : ℝ)) (tA 12735 * 163 ^ 2 + 26 / (10 * 12735)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3653633 / 1000000000))) * ((236314943 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3653633 / 1000000000)) ^ 3) * ((92781683 / 62500000000000000000000))) + ((5004948617 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3653633 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12735) : ℝ)) d.D d.V d.P (√(tA 12735) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3653633 / 1000000000)) ^ 2 * (((1087002629 / 500000000000000)) * ((7705859921 / 200000000000000000)))) + ((5004948617 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12735) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3653633 / 1000000000)) * ((236314943 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12735) : ℝ)) (tA 12735 * 163 ^ 2 + 26 / (10 * 12735)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((236314943 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3653633 / 1000000000)) ^ 2) * ((92781683 / 62500000000000000000000)) + ((5004948617 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12735) : ℝ)) (√(26 / (10 * 12735) : ℝ)) d.D d.V d.P (√(tA 12735) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3653633 / 1000000000)) * (((1087002629 / 500000000000000)) * ((7705859921 / 200000000000000000))) + ((5004948617 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12735) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((236314943 / 50000000000000000000) : ℝ) + ((5004948617 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12735

namespace BstLean.Part266.Row12735
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12735 163 ∧
    0 ≤ (tableEnvelope C).f1 12735 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12735 163 ∧
    0 ≤ (tableEnvelope C).w1 12735 163 ∧ 0 ≤ (tableEnvelope C).w2 12735 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12735 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12735 163 ∧ 0 ≤ d.f1 12735 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12735 163 ∧ 0 ≤ d.w1 12735 163 ∧ 0 ≤ d.w2 12735 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12735 ≤ 2 * (228 / 100 : ℝ) / 12735 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12735 ≤ 2 * (370 / 100 : ℝ) / 12735 := by
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
    (completeRAData (tableEnvelope C) 12735 163).locationBound 12735 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12735 163).energyBound 12735 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12735 163) (d.f1 12735 163) d.f2 ≤
      32 * (((4551278489 / 1000000000000000000) : ℝ) + (1518383533 / 1000000000000000000) + (364944039 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12735 163) (d.w1 12735 163)
      (d.w2 12735 163) ≤
      32 * (((181812531 / 10000000000000000000) : ℝ) + (646780707 / 50000000000000000000) + (94526947 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12735 163) (d.f1 12735 163) d.f2 ≤
      ((4551278489 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4551278489 / 1000000000000000000)) * ((1518383533 / 1000000000000000000)) * (126 / 100) +
      2 * (((1518383533 / 1000000000000000000)) ^ 2 + 2 * ((4551278489 / 1000000000000000000)) * ((364944039 / 1000000000000000000))) +
      6 * ((1518383533 / 1000000000000000000)) * ((364944039 / 1000000000000000000)) * (126 / 100) + 8 * ((364944039 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12735 163) (d.f1 12735 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12735 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12735 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12735 163) (d.f1 12735 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12735 163) (d.w1 12735 163) (d.w2 12735 163)
  have hwexpr0 : 0 ≤ d.w0 12735 163 + d.w1 12735 163 * √(π / 2) +
      2 * d.w2 12735 163 + energyR16 12735 *
      radiusPolynomialRoot16 (d.w0 12735 163) (d.w1 12735 163) (d.w2 12735 163) := by
    positivity
  constructor
  · change (12735 : ℝ) ^ 8 * (mA 12735 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12735 163) (d.f1 12735 163) d.f2 + locationR16 12735 *
        radiusPolynomialRoot16 (d.f0 12735 163) (d.f1 12735 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12735 : ℝ) ^ 8 * (mA 12735 : ℝ) ^ 8 *
        ((((4551278489 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4551278489 / 1000000000000000000)) * ((1518383533 / 1000000000000000000)) * (126 / 100) +
          2 * (((1518383533 / 1000000000000000000)) ^ 2 + 2 * ((4551278489 / 1000000000000000000)) * ((364944039 / 1000000000000000000))) +
          6 * ((1518383533 / 1000000000000000000)) * ((364944039 / 1000000000000000000)) * (126 / 100) + 8 * ((364944039 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12735) *
          (32 * (((4551278489 / 1000000000000000000) : ℝ) + (1518383533 / 1000000000000000000) + (364944039 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12735 : ℝ) ^ 16 *
      (d.w0 12735 163 + d.w1 12735 163 * √(π / 2) + 2 * d.w2 12735 163 +
        energyR16 12735 * radiusPolynomialRoot16 (d.w0 12735 163) (d.w1 12735 163)
          (d.w2 12735 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12735 : ℝ) ^ 16 *
        (((181812531 / 10000000000000000000) : ℝ) + ((646780707 / 50000000000000000000)) * (126 / 100) + 2 * ((94526947 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12735) *
          (32 * (((181812531 / 10000000000000000000) : ℝ) + (646780707 / 50000000000000000000) + (94526947 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12735

/-! A coarse bound on the actual paper statistics constant at dimension 12736. -/
namespace BstLean.Part266.Row12736
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12734 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12734 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12734 128 ≤ (12988 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12988 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12736) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12736 : ℕ))
    (by norm_num : (12736 : ℕ) ≤ 16384)
  have ht : paperTail256 12736 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12736 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12736 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12736 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12736 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12736 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12734 128 * √(2 / (12736 : ℝ)) *
      (√(12736 : ℝ) + paperT0 12736 + paperTail256 12736) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12736 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12736 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12736 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12734 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12734 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12736 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12736

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12736
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12736 (61 / 100) 163 (17 / (100 * 12736)) (26 / (10 * 12736)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12736 (61 / 100) 163 (17 / (100 * 12736)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (2953241 / 625000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (59361629 / 40000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (39076369 / 7812500000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12736 / 12736 * (61 / 100)) ^ 4 * inverseRadius8 (12736 - 1) /
            envelopeGap 12736 (61 / 100) 163 (17 / (100 * 12736)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12736

namespace BstLean.Part266.Row12736
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12736 163 ≤ (910076703 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12736 163 ≤ (1518085117 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (364872359 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12736 163 ≤ (1817696733 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12736 163 ≤ (323314141 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12736 163 ≤ (236261703 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (2953241 / 625000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (2953241 / 625000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (59361629 / 40000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (39076369 / 7812500000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((365349 / 100000000) : ℝ) ≤ √(17 / (100 * 12736) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12736) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (543437301 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (770464983 / 20000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12736) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12736) ≤ (55520319 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12736) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12736 * (163 : ℝ) ^ 2 + 26 / (10 * 12736) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12736) : ℝ)) (tA 12736 * 163 ^ 2 + 26 / (10 * 12736)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((365349 / 100000000))) * ((2953241 / 625000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((365349 / 100000000)) ^ 3) * ((59361629 / 40000000000000000000000))) + ((39076369 / 7812500000000000000000)) * (3 / 2 * (39895 / 100000) / ((365349 / 100000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12736) : ℝ)) d.D d.V d.P (√(tA 12736) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((365349 / 100000000)) ^ 2 * (((543437301 / 250000000000000)) * ((770464983 / 20000000000000000)))) + ((39076369 / 7812500000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12736) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((365349 / 100000000)) * ((2953241 / 625000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12736) : ℝ)) (tA 12736 * 163 ^ 2 + 26 / (10 * 12736)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((2953241 / 625000000000000000) : ℝ) + (24198 / 100000) / (2 * ((365349 / 100000000)) ^ 2) * ((59361629 / 40000000000000000000000)) + ((39076369 / 7812500000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12736) : ℝ)) (√(26 / (10 * 12736) : ℝ)) d.D d.V d.P (√(tA 12736) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((365349 / 100000000)) * (((543437301 / 250000000000000)) * ((770464983 / 20000000000000000))) + ((39076369 / 7812500000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12736) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((2953241 / 625000000000000000) : ℝ) + ((39076369 / 7812500000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12736

namespace BstLean.Part266.Row12736
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12736 163 ∧
    0 ≤ (tableEnvelope C).f1 12736 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12736 163 ∧
    0 ≤ (tableEnvelope C).w1 12736 163 ∧ 0 ≤ (tableEnvelope C).w2 12736 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12736 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12736 163 ∧ 0 ≤ d.f1 12736 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12736 163 ∧ 0 ≤ d.w1 12736 163 ∧ 0 ≤ d.w2 12736 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12736 ≤ 2 * (228 / 100 : ℝ) / 12736 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12736 ≤ 2 * (370 / 100 : ℝ) / 12736 := by
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
    (completeRAData (tableEnvelope C) 12736 163).locationBound 12736 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12736 163).energyBound 12736 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12736 163) (d.f1 12736 163) d.f2 ≤
      32 * (((910076703 / 200000000000000000) : ℝ) + (1518085117 / 1000000000000000000) + (364872359 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12736 163) (d.w1 12736 163)
      (d.w2 12736 163) ≤
      32 * (((1817696733 / 100000000000000000000) : ℝ) + (323314141 / 25000000000000000000) + (236261703 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12736 163) (d.f1 12736 163) d.f2 ≤
      ((910076703 / 200000000000000000) : ℝ) ^ 2 + 2 * ((910076703 / 200000000000000000)) * ((1518085117 / 1000000000000000000)) * (126 / 100) +
      2 * (((1518085117 / 1000000000000000000)) ^ 2 + 2 * ((910076703 / 200000000000000000)) * ((364872359 / 1000000000000000000))) +
      6 * ((1518085117 / 1000000000000000000)) * ((364872359 / 1000000000000000000)) * (126 / 100) + 8 * ((364872359 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12736 163) (d.f1 12736 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12736 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12736 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12736 163) (d.f1 12736 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12736 163) (d.w1 12736 163) (d.w2 12736 163)
  have hwexpr0 : 0 ≤ d.w0 12736 163 + d.w1 12736 163 * √(π / 2) +
      2 * d.w2 12736 163 + energyR16 12736 *
      radiusPolynomialRoot16 (d.w0 12736 163) (d.w1 12736 163) (d.w2 12736 163) := by
    positivity
  constructor
  · change (12736 : ℝ) ^ 8 * (mA 12736 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12736 163) (d.f1 12736 163) d.f2 + locationR16 12736 *
        radiusPolynomialRoot16 (d.f0 12736 163) (d.f1 12736 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12736 : ℝ) ^ 8 * (mA 12736 : ℝ) ^ 8 *
        ((((910076703 / 200000000000000000) : ℝ) ^ 2 + 2 * ((910076703 / 200000000000000000)) * ((1518085117 / 1000000000000000000)) * (126 / 100) +
          2 * (((1518085117 / 1000000000000000000)) ^ 2 + 2 * ((910076703 / 200000000000000000)) * ((364872359 / 1000000000000000000))) +
          6 * ((1518085117 / 1000000000000000000)) * ((364872359 / 1000000000000000000)) * (126 / 100) + 8 * ((364872359 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12736) *
          (32 * (((910076703 / 200000000000000000) : ℝ) + (1518085117 / 1000000000000000000) + (364872359 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12736 : ℝ) ^ 16 *
      (d.w0 12736 163 + d.w1 12736 163 * √(π / 2) + 2 * d.w2 12736 163 +
        energyR16 12736 * radiusPolynomialRoot16 (d.w0 12736 163) (d.w1 12736 163)
          (d.w2 12736 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12736 : ℝ) ^ 16 *
        (((1817696733 / 100000000000000000000) : ℝ) + ((323314141 / 25000000000000000000)) * (126 / 100) + 2 * ((236261703 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12736) *
          (32 * (((1817696733 / 100000000000000000000) : ℝ) + (323314141 / 25000000000000000000) + (236261703 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12736

/-! A coarse bound on the actual paper statistics constant at dimension 12737. -/
namespace BstLean.Part266.Row12737
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12735 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12735 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12735 128 ≤ (12989 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12989 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12737) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12737 : ℕ))
    (by norm_num : (12737 : ℕ) ≤ 16384)
  have ht : paperTail256 12737 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12737 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12737 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12737 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12737 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12737 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12735 128 * √(2 / (12737 : ℝ)) *
      (√(12737 : ℝ) + paperT0 12737 + paperTail256 12737) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12737 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12737 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12737 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12735 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12735 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12737 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12737

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12737
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12737 (61 / 100) 163 (17 / (100 * 12737)) (26 / (10 * 12737)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12737 (61 / 100) 163 (17 / (100 * 12737)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (472407269 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (296714941 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2499302057 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12737 / 12737 * (61 / 100)) ^ 4 * inverseRadius8 (12737 - 1) /
            envelopeGap 12737 (61 / 100) 163 (17 / (100 * 12737)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12737

namespace BstLean.Part266.Row12737
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12737 163 ≤ (2274746221 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12737 163 ≤ (379446907 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (456001 / 1250000000000000)
  w0 : (tableEnvelope C).w0 12737 163 ≤ (1817269039 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12737 163 ≤ (129295217 / 10000000000000000000)
  w2 : (tableEnvelope C).w2 12737 163 ≤ (29525757 / 6250000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (472407269 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (472407269 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (296714941 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2499302057 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1826673 / 500000000) : ℝ) ≤ √(17 / (100 * 12737) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12737) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (5433733 / 2500000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38517200119 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12737) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12737) ≤ (1387899 / 12500000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12737) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12737 * (163 : ℝ) ^ 2 + 26 / (10 * 12737) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12737) : ℝ)) (tA 12737 * 163 ^ 2 + 26 / (10 * 12737)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1826673 / 500000000))) * ((472407269 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1826673 / 500000000)) ^ 3) * ((296714941 / 200000000000000000000000))) + ((2499302057 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1826673 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12737) : ℝ)) d.D d.V d.P (√(tA 12737) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1826673 / 500000000)) ^ 2 * (((5433733 / 2500000000000)) * ((38517200119 / 1000000000000000000)))) + ((2499302057 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12737) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1826673 / 500000000)) * ((472407269 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12737) : ℝ)) (tA 12737 * 163 ^ 2 + 26 / (10 * 12737)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((472407269 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1826673 / 500000000)) ^ 2) * ((296714941 / 200000000000000000000000)) + ((2499302057 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12737) : ℝ)) (√(26 / (10 * 12737) : ℝ)) d.D d.V d.P (√(tA 12737) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1826673 / 500000000)) * (((5433733 / 2500000000000)) * ((38517200119 / 1000000000000000000))) + ((2499302057 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12737) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((472407269 / 100000000000000000000) : ℝ) + ((2499302057 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12737

namespace BstLean.Part266.Row12737
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12737 163 ∧
    0 ≤ (tableEnvelope C).f1 12737 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12737 163 ∧
    0 ≤ (tableEnvelope C).w1 12737 163 ∧ 0 ≤ (tableEnvelope C).w2 12737 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12737 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12737 163 ∧ 0 ≤ d.f1 12737 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12737 163 ∧ 0 ≤ d.w1 12737 163 ∧ 0 ≤ d.w2 12737 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12737 ≤ 2 * (228 / 100 : ℝ) / 12737 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12737 ≤ 2 * (370 / 100 : ℝ) / 12737 := by
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
    (completeRAData (tableEnvelope C) 12737 163).locationBound 12737 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12737 163).energyBound 12737 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12737 163) (d.f1 12737 163) d.f2 ≤
      32 * (((2274746221 / 500000000000000000) : ℝ) + (379446907 / 250000000000000000) + (456001 / 1250000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12737 163) (d.w1 12737 163)
      (d.w2 12737 163) ≤
      32 * (((1817269039 / 100000000000000000000) : ℝ) + (129295217 / 10000000000000000000) + (29525757 / 6250000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12737 163) (d.f1 12737 163) d.f2 ≤
      ((2274746221 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2274746221 / 500000000000000000)) * ((379446907 / 250000000000000000)) * (126 / 100) +
      2 * (((379446907 / 250000000000000000)) ^ 2 + 2 * ((2274746221 / 500000000000000000)) * ((456001 / 1250000000000000))) +
      6 * ((379446907 / 250000000000000000)) * ((456001 / 1250000000000000)) * (126 / 100) + 8 * ((456001 / 1250000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12737 163) (d.f1 12737 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12737 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12737 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12737 163) (d.f1 12737 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12737 163) (d.w1 12737 163) (d.w2 12737 163)
  have hwexpr0 : 0 ≤ d.w0 12737 163 + d.w1 12737 163 * √(π / 2) +
      2 * d.w2 12737 163 + energyR16 12737 *
      radiusPolynomialRoot16 (d.w0 12737 163) (d.w1 12737 163) (d.w2 12737 163) := by
    positivity
  constructor
  · change (12737 : ℝ) ^ 8 * (mA 12737 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12737 163) (d.f1 12737 163) d.f2 + locationR16 12737 *
        radiusPolynomialRoot16 (d.f0 12737 163) (d.f1 12737 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12737 : ℝ) ^ 8 * (mA 12737 : ℝ) ^ 8 *
        ((((2274746221 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2274746221 / 500000000000000000)) * ((379446907 / 250000000000000000)) * (126 / 100) +
          2 * (((379446907 / 250000000000000000)) ^ 2 + 2 * ((2274746221 / 500000000000000000)) * ((456001 / 1250000000000000))) +
          6 * ((379446907 / 250000000000000000)) * ((456001 / 1250000000000000)) * (126 / 100) + 8 * ((456001 / 1250000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12737) *
          (32 * (((2274746221 / 500000000000000000) : ℝ) + (379446907 / 250000000000000000) + (456001 / 1250000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12737 : ℝ) ^ 16 *
      (d.w0 12737 163 + d.w1 12737 163 * √(π / 2) + 2 * d.w2 12737 163 +
        energyR16 12737 * radiusPolynomialRoot16 (d.w0 12737 163) (d.w1 12737 163)
          (d.w2 12737 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12737 : ℝ) ^ 16 *
        (((1817269039 / 100000000000000000000) : ℝ) + ((129295217 / 10000000000000000000)) * (126 / 100) + 2 * ((29525757 / 6250000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12737) *
          (32 * (((1817269039 / 100000000000000000000) : ℝ) + (129295217 / 10000000000000000000) + (29525757 / 6250000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12737

/-! A coarse bound on the actual paper statistics constant at dimension 12738. -/
namespace BstLean.Part266.Row12738
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12736 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12736 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12736 128 ≤ (12990 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12990 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12738) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12738 : ℕ))
    (by norm_num : (12738 : ℕ) ≤ 16384)
  have ht : paperTail256 12738 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12738 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12738 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12738 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12738 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12738 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12736 128 * √(2 / (12738 : ℝ)) *
      (√(12738 : ℝ) + paperT0 12738 + paperTail256 12738) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12738 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12738 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12738 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12736 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12736 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12738 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12738

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12738
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12738 (61 / 100) 163 (17 / (100 * 12738)) (26 / (10 * 12738)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12738 (61 / 100) 163 (17 / (100 * 12738)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (118074003 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (370777217 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4995435259 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12738 / 12738 * (61 / 100)) ^ 4 * inverseRadius8 (12738 - 1) /
            envelopeGap 12738 (61 / 100) 163 (17 / (100 * 12738)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12738

namespace BstLean.Part266.Row12738
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12738 163 ≤ (4548598081 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12738 163 ≤ (1517489403 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (182364581 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12738 163 ≤ (908420377 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12738 163 ≤ (1292647523 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12738 163 ≤ (118075213 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (118074003 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (118074003 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (370777217 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4995435259 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3653203 / 1000000000) : ℝ) ≤ √(17 / (100 * 12738) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12738) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (434647449 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7702230503 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12738) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12738) ≤ (27755801 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12738) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12738 * (163 : ℝ) ^ 2 + 26 / (10 * 12738) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12738) : ℝ)) (tA 12738 * 163 ^ 2 + 26 / (10 * 12738)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3653203 / 1000000000))) * ((118074003 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3653203 / 1000000000)) ^ 3) * ((370777217 / 250000000000000000000000))) + ((4995435259 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3653203 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12738) : ℝ)) d.D d.V d.P (√(tA 12738) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3653203 / 1000000000)) ^ 2 * (((434647449 / 200000000000000)) * ((7702230503 / 200000000000000000)))) + ((4995435259 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12738) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3653203 / 1000000000)) * ((118074003 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12738) : ℝ)) (tA 12738 * 163 ^ 2 + 26 / (10 * 12738)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((118074003 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3653203 / 1000000000)) ^ 2) * ((370777217 / 250000000000000000000000)) + ((4995435259 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12738) : ℝ)) (√(26 / (10 * 12738) : ℝ)) d.D d.V d.P (√(tA 12738) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3653203 / 1000000000)) * (((434647449 / 200000000000000)) * ((7702230503 / 200000000000000000))) + ((4995435259 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12738) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((118074003 / 25000000000000000000) : ℝ) + ((4995435259 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12738

namespace BstLean.Part266.Row12738
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12738 163 ∧
    0 ≤ (tableEnvelope C).f1 12738 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12738 163 ∧
    0 ≤ (tableEnvelope C).w1 12738 163 ∧ 0 ≤ (tableEnvelope C).w2 12738 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12738 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12738 163 ∧ 0 ≤ d.f1 12738 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12738 163 ∧ 0 ≤ d.w1 12738 163 ∧ 0 ≤ d.w2 12738 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12738 ≤ 2 * (228 / 100 : ℝ) / 12738 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12738 ≤ 2 * (370 / 100 : ℝ) / 12738 := by
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
    (completeRAData (tableEnvelope C) 12738 163).locationBound 12738 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12738 163).energyBound 12738 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12738 163) (d.f1 12738 163) d.f2 ≤
      32 * (((4548598081 / 1000000000000000000) : ℝ) + (1517489403 / 1000000000000000000) + (182364581 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12738 163) (d.w1 12738 163)
      (d.w2 12738 163) ≤
      32 * (((908420377 / 50000000000000000000) : ℝ) + (1292647523 / 100000000000000000000) + (118075213 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12738 163) (d.f1 12738 163) d.f2 ≤
      ((4548598081 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4548598081 / 1000000000000000000)) * ((1517489403 / 1000000000000000000)) * (126 / 100) +
      2 * (((1517489403 / 1000000000000000000)) ^ 2 + 2 * ((4548598081 / 1000000000000000000)) * ((182364581 / 500000000000000000))) +
      6 * ((1517489403 / 1000000000000000000)) * ((182364581 / 500000000000000000)) * (126 / 100) + 8 * ((182364581 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12738 163) (d.f1 12738 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12738 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12738 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12738 163) (d.f1 12738 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12738 163) (d.w1 12738 163) (d.w2 12738 163)
  have hwexpr0 : 0 ≤ d.w0 12738 163 + d.w1 12738 163 * √(π / 2) +
      2 * d.w2 12738 163 + energyR16 12738 *
      radiusPolynomialRoot16 (d.w0 12738 163) (d.w1 12738 163) (d.w2 12738 163) := by
    positivity
  constructor
  · change (12738 : ℝ) ^ 8 * (mA 12738 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12738 163) (d.f1 12738 163) d.f2 + locationR16 12738 *
        radiusPolynomialRoot16 (d.f0 12738 163) (d.f1 12738 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12738 : ℝ) ^ 8 * (mA 12738 : ℝ) ^ 8 *
        ((((4548598081 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4548598081 / 1000000000000000000)) * ((1517489403 / 1000000000000000000)) * (126 / 100) +
          2 * (((1517489403 / 1000000000000000000)) ^ 2 + 2 * ((4548598081 / 1000000000000000000)) * ((182364581 / 500000000000000000))) +
          6 * ((1517489403 / 1000000000000000000)) * ((182364581 / 500000000000000000)) * (126 / 100) + 8 * ((182364581 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12738) *
          (32 * (((4548598081 / 1000000000000000000) : ℝ) + (1517489403 / 1000000000000000000) + (182364581 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12738 : ℝ) ^ 16 *
      (d.w0 12738 163 + d.w1 12738 163 * √(π / 2) + 2 * d.w2 12738 163 +
        energyR16 12738 * radiusPolynomialRoot16 (d.w0 12738 163) (d.w1 12738 163)
          (d.w2 12738 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12738 : ℝ) ^ 16 *
        (((908420377 / 50000000000000000000) : ℝ) + ((1292647523 / 100000000000000000000)) * (126 / 100) + 2 * ((118075213 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12738) *
          (32 * (((908420377 / 50000000000000000000) : ℝ) + (1292647523 / 100000000000000000000) + (118075213 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12738

/-! A coarse bound on the actual paper statistics constant at dimension 12739. -/
namespace BstLean.Part266.Row12739
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12737 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12737 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12737 128 ≤ (12991 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12991 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12739) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12739 : ℕ))
    (by norm_num : (12739 : ℕ) ≤ 16384)
  have ht : paperTail256 12739 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12739 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12739 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12739 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12739 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12739 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12737 128 * √(2 / (12739 : ℝ)) *
      (√(12739 : ℝ) + paperT0 12739 + paperTail256 12739) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12739 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12739 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12739 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12737 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12737 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12739 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12739

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12739
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12739 (61 / 100) 163 (17 / (100 * 12739)) (26 / (10 * 12739)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12739 (61 / 100) 163 (17 / (100 * 12739)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (472184791 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1482643213 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4992268667 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12739 / 12739 * (61 / 100)) ^ 4 * inverseRadius8 (12739 - 1) /
            envelopeGap 12739 (61 / 100) 163 (17 / (100 * 12739)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12739

namespace BstLean.Part266.Row12739
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12739 163 ≤ (4547707617 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12739 163 ≤ (303438421 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (182328823 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12739 163 ≤ (1816413353 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12739 163 ≤ (323085833 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12739 163 ≤ (472189627 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (472184791 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (472184791 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1482643213 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4992268667 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3653059 / 1000000000) : ℝ) ≤ √(17 / (100 * 12739) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12739) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1086490671 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9626276581 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12739) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12739) ≤ (13876811 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12739) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12739 * (163 : ℝ) ^ 2 + 26 / (10 * 12739) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12739) : ℝ)) (tA 12739 * 163 ^ 2 + 26 / (10 * 12739)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3653059 / 1000000000))) * ((472184791 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3653059 / 1000000000)) ^ 3) * ((1482643213 / 1000000000000000000000000))) + ((4992268667 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3653059 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12739) : ℝ)) d.D d.V d.P (√(tA 12739) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3653059 / 1000000000)) ^ 2 * (((1086490671 / 500000000000000)) * ((9626276581 / 250000000000000000)))) + ((4992268667 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12739) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3653059 / 1000000000)) * ((472184791 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12739) : ℝ)) (tA 12739 * 163 ^ 2 + 26 / (10 * 12739)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((472184791 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3653059 / 1000000000)) ^ 2) * ((1482643213 / 1000000000000000000000000)) + ((4992268667 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12739) : ℝ)) (√(26 / (10 * 12739) : ℝ)) d.D d.V d.P (√(tA 12739) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3653059 / 1000000000)) * (((1086490671 / 500000000000000)) * ((9626276581 / 250000000000000000))) + ((4992268667 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12739) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((472184791 / 100000000000000000000) : ℝ) + ((4992268667 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12739

namespace BstLean.Part266.Row12739
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12739 163 ∧
    0 ≤ (tableEnvelope C).f1 12739 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12739 163 ∧
    0 ≤ (tableEnvelope C).w1 12739 163 ∧ 0 ≤ (tableEnvelope C).w2 12739 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12739 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12739 163 ∧ 0 ≤ d.f1 12739 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12739 163 ∧ 0 ≤ d.w1 12739 163 ∧ 0 ≤ d.w2 12739 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12739 ≤ 2 * (228 / 100 : ℝ) / 12739 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12739 ≤ 2 * (370 / 100 : ℝ) / 12739 := by
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
    (completeRAData (tableEnvelope C) 12739 163).locationBound 12739 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12739 163).energyBound 12739 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12739 163) (d.f1 12739 163) d.f2 ≤
      32 * (((4547707617 / 1000000000000000000) : ℝ) + (303438421 / 200000000000000000) + (182328823 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12739 163) (d.w1 12739 163)
      (d.w2 12739 163) ≤
      32 * (((1816413353 / 100000000000000000000) : ℝ) + (323085833 / 25000000000000000000) + (472189627 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12739 163) (d.f1 12739 163) d.f2 ≤
      ((4547707617 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4547707617 / 1000000000000000000)) * ((303438421 / 200000000000000000)) * (126 / 100) +
      2 * (((303438421 / 200000000000000000)) ^ 2 + 2 * ((4547707617 / 1000000000000000000)) * ((182328823 / 500000000000000000))) +
      6 * ((303438421 / 200000000000000000)) * ((182328823 / 500000000000000000)) * (126 / 100) + 8 * ((182328823 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12739 163) (d.f1 12739 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12739 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12739 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12739 163) (d.f1 12739 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12739 163) (d.w1 12739 163) (d.w2 12739 163)
  have hwexpr0 : 0 ≤ d.w0 12739 163 + d.w1 12739 163 * √(π / 2) +
      2 * d.w2 12739 163 + energyR16 12739 *
      radiusPolynomialRoot16 (d.w0 12739 163) (d.w1 12739 163) (d.w2 12739 163) := by
    positivity
  constructor
  · change (12739 : ℝ) ^ 8 * (mA 12739 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12739 163) (d.f1 12739 163) d.f2 + locationR16 12739 *
        radiusPolynomialRoot16 (d.f0 12739 163) (d.f1 12739 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12739 : ℝ) ^ 8 * (mA 12739 : ℝ) ^ 8 *
        ((((4547707617 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4547707617 / 1000000000000000000)) * ((303438421 / 200000000000000000)) * (126 / 100) +
          2 * (((303438421 / 200000000000000000)) ^ 2 + 2 * ((4547707617 / 1000000000000000000)) * ((182328823 / 500000000000000000))) +
          6 * ((303438421 / 200000000000000000)) * ((182328823 / 500000000000000000)) * (126 / 100) + 8 * ((182328823 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12739) *
          (32 * (((4547707617 / 1000000000000000000) : ℝ) + (303438421 / 200000000000000000) + (182328823 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12739 : ℝ) ^ 16 *
      (d.w0 12739 163 + d.w1 12739 163 * √(π / 2) + 2 * d.w2 12739 163 +
        energyR16 12739 * radiusPolynomialRoot16 (d.w0 12739 163) (d.w1 12739 163)
          (d.w2 12739 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12739 : ℝ) ^ 16 *
        (((1816413353 / 100000000000000000000) : ℝ) + ((323085833 / 25000000000000000000)) * (126 / 100) + 2 * ((472189627 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12739) *
          (32 * (((1816413353 / 100000000000000000000) : ℝ) + (323085833 / 25000000000000000000) + (472189627 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12739

/-! A coarse bound on the actual paper statistics constant at dimension 12740. -/
namespace BstLean.Part266.Row12740
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12738 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12738 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12738 128 ≤ (12992 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12992 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12740) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12740 : ℕ))
    (by norm_num : (12740 : ℕ) ≤ 16384)
  have ht : paperTail256 12740 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12740 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12740 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12740 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12740 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12740 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12738 128 * √(2 / (12740 : ℝ)) *
      (√(12740 : ℝ) + paperT0 12740 + paperTail256 12740) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12740 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12740 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12740 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12738 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12738 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12740 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12740

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12740
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12740 (61 / 100) 163 (17 / (100 * 12740)) (26 / (10 * 12740)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12740 (61 / 100) 163 (17 / (100 * 12740)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (118018401 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (741088871 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2494552167 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12740 / 12740 * (61 / 100)) ^ 4 * inverseRadius8 (12740 - 1) /
            envelopeGap 12740 (61 / 100) 163 (17 / (100 * 12740)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12740

namespace BstLean.Part266.Row12740
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12740 163 ≤ (4546813869 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12740 163 ≤ (189611759 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (7291721 / 20000000000000000)
  w0 : (tableEnvelope C).w0 12740 163 ≤ (1815985363 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12740 163 ≤ (161504861 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 12740 163 ≤ (472078437 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (118018401 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (118018401 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (741088871 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2494552167 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((913229 / 250000000) : ℝ) ≤ √(17 / (100 * 12740) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12740) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2172725487 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38499061573 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12740) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12740) ≤ (4440231 / 40000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12740) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12740 * (163 : ℝ) ^ 2 + 26 / (10 * 12740) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12740) : ℝ)) (tA 12740 * 163 ^ 2 + 26 / (10 * 12740)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((913229 / 250000000))) * ((118018401 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((913229 / 250000000)) ^ 3) * ((741088871 / 500000000000000000000000))) + ((2494552167 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((913229 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12740) : ℝ)) d.D d.V d.P (√(tA 12740) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((913229 / 250000000)) ^ 2 * (((2172725487 / 1000000000000000)) * ((38499061573 / 1000000000000000000)))) + ((2494552167 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12740) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((913229 / 250000000)) * ((118018401 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12740) : ℝ)) (tA 12740 * 163 ^ 2 + 26 / (10 * 12740)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((118018401 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((913229 / 250000000)) ^ 2) * ((741088871 / 500000000000000000000000)) + ((2494552167 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12740) : ℝ)) (√(26 / (10 * 12740) : ℝ)) d.D d.V d.P (√(tA 12740) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((913229 / 250000000)) * (((2172725487 / 1000000000000000)) * ((38499061573 / 1000000000000000000))) + ((2494552167 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12740) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((118018401 / 25000000000000000000) : ℝ) + ((2494552167 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12740

namespace BstLean.Part266.Row12740
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12740 163 ∧
    0 ≤ (tableEnvelope C).f1 12740 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12740 163 ∧
    0 ≤ (tableEnvelope C).w1 12740 163 ∧ 0 ≤ (tableEnvelope C).w2 12740 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12740 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12740 163 ∧ 0 ≤ d.f1 12740 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12740 163 ∧ 0 ≤ d.w1 12740 163 ∧ 0 ≤ d.w2 12740 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12740 ≤ 2 * (228 / 100 : ℝ) / 12740 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12740 ≤ 2 * (370 / 100 : ℝ) / 12740 := by
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
    (completeRAData (tableEnvelope C) 12740 163).locationBound 12740 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12740 163).energyBound 12740 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12740 163) (d.f1 12740 163) d.f2 ≤
      32 * (((4546813869 / 1000000000000000000) : ℝ) + (189611759 / 125000000000000000) + (7291721 / 20000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12740 163) (d.w1 12740 163)
      (d.w2 12740 163) ≤
      32 * (((1815985363 / 100000000000000000000) : ℝ) + (161504861 / 12500000000000000000) + (472078437 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12740 163) (d.f1 12740 163) d.f2 ≤
      ((4546813869 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4546813869 / 1000000000000000000)) * ((189611759 / 125000000000000000)) * (126 / 100) +
      2 * (((189611759 / 125000000000000000)) ^ 2 + 2 * ((4546813869 / 1000000000000000000)) * ((7291721 / 20000000000000000))) +
      6 * ((189611759 / 125000000000000000)) * ((7291721 / 20000000000000000)) * (126 / 100) + 8 * ((7291721 / 20000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12740 163) (d.f1 12740 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12740 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12740 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12740 163) (d.f1 12740 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12740 163) (d.w1 12740 163) (d.w2 12740 163)
  have hwexpr0 : 0 ≤ d.w0 12740 163 + d.w1 12740 163 * √(π / 2) +
      2 * d.w2 12740 163 + energyR16 12740 *
      radiusPolynomialRoot16 (d.w0 12740 163) (d.w1 12740 163) (d.w2 12740 163) := by
    positivity
  constructor
  · change (12740 : ℝ) ^ 8 * (mA 12740 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12740 163) (d.f1 12740 163) d.f2 + locationR16 12740 *
        radiusPolynomialRoot16 (d.f0 12740 163) (d.f1 12740 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12740 : ℝ) ^ 8 * (mA 12740 : ℝ) ^ 8 *
        ((((4546813869 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4546813869 / 1000000000000000000)) * ((189611759 / 125000000000000000)) * (126 / 100) +
          2 * (((189611759 / 125000000000000000)) ^ 2 + 2 * ((4546813869 / 1000000000000000000)) * ((7291721 / 20000000000000000))) +
          6 * ((189611759 / 125000000000000000)) * ((7291721 / 20000000000000000)) * (126 / 100) + 8 * ((7291721 / 20000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12740) *
          (32 * (((4546813869 / 1000000000000000000) : ℝ) + (189611759 / 125000000000000000) + (7291721 / 20000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12740 : ℝ) ^ 16 *
      (d.w0 12740 163 + d.w1 12740 163 * √(π / 2) + 2 * d.w2 12740 163 +
        energyR16 12740 * radiusPolynomialRoot16 (d.w0 12740 163) (d.w1 12740 163)
          (d.w2 12740 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12740 : ℝ) ^ 16 *
        (((1815985363 / 100000000000000000000) : ℝ) + ((161504861 / 12500000000000000000)) * (126 / 100) + 2 * ((472078437 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12740) *
          (32 * (((1815985363 / 100000000000000000000) : ℝ) + (161504861 / 12500000000000000000) + (472078437 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12740

/-! A coarse bound on the actual paper statistics constant at dimension 12741. -/
namespace BstLean.Part266.Row12741
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12739 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12739 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12739 128 ≤ (12993 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12993 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12741) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12741 : ℕ))
    (by norm_num : (12741 : ℕ) ≤ 16384)
  have ht : paperTail256 12741 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12741 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12741 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12741 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12741 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12741 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12739 128 * √(2 / (12741 : ℝ)) *
      (√(12741 : ℝ) + paperT0 12741 + paperTail256 12741) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12741 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12741 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12741 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12739 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12739 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12741 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12741

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12741
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12741 (61 / 100) 163 (17 / (100 * 12741)) (26 / (10 * 12741)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12741 (61 / 100) 163 (17 / (100 * 12741)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (117990613 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1481712453 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4985942261 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12741 / 12741 * (61 / 100)) ^ 4 * inverseRadius8 (12741 - 1) /
            envelopeGap 12741 (61 / 100) 163 (17 / (100 * 12741)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12741

namespace BstLean.Part266.Row12741
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12741 163 ≤ (2272960213 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12741 163 ≤ (303319227 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (91128619 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12741 163 ≤ (1815557519 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12741 163 ≤ (645867273 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12741 163 ≤ (235983641 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (117990613 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (117990613 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1481712453 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4985942261 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3652773 / 1000000000) : ℝ) ≤ √(17 / (100 * 12741) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12741) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2172469683 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19246509119 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12741) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12741) ≤ (55498531 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12741) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12741 * (163 : ℝ) ^ 2 + 26 / (10 * 12741) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12741) : ℝ)) (tA 12741 * 163 ^ 2 + 26 / (10 * 12741)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3652773 / 1000000000))) * ((117990613 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3652773 / 1000000000)) ^ 3) * ((1481712453 / 1000000000000000000000000))) + ((4985942261 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3652773 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12741) : ℝ)) d.D d.V d.P (√(tA 12741) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3652773 / 1000000000)) ^ 2 * (((2172469683 / 1000000000000000)) * ((19246509119 / 500000000000000000)))) + ((4985942261 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12741) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3652773 / 1000000000)) * ((117990613 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12741) : ℝ)) (tA 12741 * 163 ^ 2 + 26 / (10 * 12741)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((117990613 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3652773 / 1000000000)) ^ 2) * ((1481712453 / 1000000000000000000000000)) + ((4985942261 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12741) : ℝ)) (√(26 / (10 * 12741) : ℝ)) d.D d.V d.P (√(tA 12741) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3652773 / 1000000000)) * (((2172469683 / 1000000000000000)) * ((19246509119 / 500000000000000000))) + ((4985942261 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12741) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((117990613 / 25000000000000000000) : ℝ) + ((4985942261 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12741

namespace BstLean.Part266.Row12741
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12741 163 ∧
    0 ≤ (tableEnvelope C).f1 12741 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12741 163 ∧
    0 ≤ (tableEnvelope C).w1 12741 163 ∧ 0 ≤ (tableEnvelope C).w2 12741 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12741 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12741 163 ∧ 0 ≤ d.f1 12741 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12741 163 ∧ 0 ≤ d.w1 12741 163 ∧ 0 ≤ d.w2 12741 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12741 ≤ 2 * (228 / 100 : ℝ) / 12741 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12741 ≤ 2 * (370 / 100 : ℝ) / 12741 := by
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
    (completeRAData (tableEnvelope C) 12741 163).locationBound 12741 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12741 163).energyBound 12741 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12741 163) (d.f1 12741 163) d.f2 ≤
      32 * (((2272960213 / 500000000000000000) : ℝ) + (303319227 / 200000000000000000) + (91128619 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12741 163) (d.w1 12741 163)
      (d.w2 12741 163) ≤
      32 * (((1815557519 / 100000000000000000000) : ℝ) + (645867273 / 50000000000000000000) + (235983641 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12741 163) (d.f1 12741 163) d.f2 ≤
      ((2272960213 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2272960213 / 500000000000000000)) * ((303319227 / 200000000000000000)) * (126 / 100) +
      2 * (((303319227 / 200000000000000000)) ^ 2 + 2 * ((2272960213 / 500000000000000000)) * ((91128619 / 250000000000000000))) +
      6 * ((303319227 / 200000000000000000)) * ((91128619 / 250000000000000000)) * (126 / 100) + 8 * ((91128619 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12741 163) (d.f1 12741 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12741 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12741 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12741 163) (d.f1 12741 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12741 163) (d.w1 12741 163) (d.w2 12741 163)
  have hwexpr0 : 0 ≤ d.w0 12741 163 + d.w1 12741 163 * √(π / 2) +
      2 * d.w2 12741 163 + energyR16 12741 *
      radiusPolynomialRoot16 (d.w0 12741 163) (d.w1 12741 163) (d.w2 12741 163) := by
    positivity
  constructor
  · change (12741 : ℝ) ^ 8 * (mA 12741 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12741 163) (d.f1 12741 163) d.f2 + locationR16 12741 *
        radiusPolynomialRoot16 (d.f0 12741 163) (d.f1 12741 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12741 : ℝ) ^ 8 * (mA 12741 : ℝ) ^ 8 *
        ((((2272960213 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2272960213 / 500000000000000000)) * ((303319227 / 200000000000000000)) * (126 / 100) +
          2 * (((303319227 / 200000000000000000)) ^ 2 + 2 * ((2272960213 / 500000000000000000)) * ((91128619 / 250000000000000000))) +
          6 * ((303319227 / 200000000000000000)) * ((91128619 / 250000000000000000)) * (126 / 100) + 8 * ((91128619 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12741) *
          (32 * (((2272960213 / 500000000000000000) : ℝ) + (303319227 / 200000000000000000) + (91128619 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12741 : ℝ) ^ 16 *
      (d.w0 12741 163 + d.w1 12741 163 * √(π / 2) + 2 * d.w2 12741 163 +
        energyR16 12741 * radiusPolynomialRoot16 (d.w0 12741 163) (d.w1 12741 163)
          (d.w2 12741 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12741 : ℝ) ^ 16 *
        (((1815557519 / 100000000000000000000) : ℝ) + ((645867273 / 50000000000000000000)) * (126 / 100) + 2 * ((235983641 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12741) *
          (32 * (((1815557519 / 100000000000000000000) : ℝ) + (645867273 / 50000000000000000000) + (235983641 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12741

/-! A coarse bound on the actual paper statistics constant at dimension 12742. -/
namespace BstLean.Part266.Row12742
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12740 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12740 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12740 128 ≤ (12994 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12994 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12742) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12742 : ℕ))
    (by norm_num : (12742 : ℕ) ≤ 16384)
  have ht : paperTail256 12742 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12742 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12742 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12742 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12742 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12742 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12740 128 * √(2 / (12742 : ℝ)) *
      (√(12742 : ℝ) + paperT0 12742 + paperTail256 12742) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12742 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12742 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12742 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12740 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12740 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12742 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12742

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12742
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12742 (61 / 100) 163 (17 / (100 * 12742)) (26 / (10 * 12742)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12742 (61 / 100) 163 (17 / (100 * 12742)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (58981417 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1481247347 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1245695611 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12742 / 12742 * (61 / 100)) ^ 4 * inverseRadius8 (12742 - 1) /
            envelopeGap 12742 (61 / 100) 163 (17 / (100 * 12742)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12742

namespace BstLean.Part266.Row12742
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12742 163 ≤ (2272515441 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12742 163 ≤ (12130393 / 8000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (22777689 / 62500000000000000)
  w0 : (tableEnvelope C).w0 12742 163 ≤ (1815130559 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12742 163 ≤ (64571533 / 5000000000000000000)
  w2 : (tableEnvelope C).w2 12742 163 ≤ (471856163 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (58981417 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (58981417 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1481247347 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1245695611 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3652629 / 1000000000) : ℝ) ≤ √(17 / (100 * 12742) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12742) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2172213931 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3848697633 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12742) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12742) ≤ (110988351 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12742) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12742 * (163 : ℝ) ^ 2 + 26 / (10 * 12742) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12742) : ℝ)) (tA 12742 * 163 ^ 2 + 26 / (10 * 12742)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3652629 / 1000000000))) * ((58981417 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3652629 / 1000000000)) ^ 3) * ((1481247347 / 1000000000000000000000000))) + ((1245695611 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3652629 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12742) : ℝ)) d.D d.V d.P (√(tA 12742) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3652629 / 1000000000)) ^ 2 * (((2172213931 / 1000000000000000)) * ((3848697633 / 100000000000000000)))) + ((1245695611 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12742) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3652629 / 1000000000)) * ((58981417 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12742) : ℝ)) (tA 12742 * 163 ^ 2 + 26 / (10 * 12742)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((58981417 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3652629 / 1000000000)) ^ 2) * ((1481247347 / 1000000000000000000000000)) + ((1245695611 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12742) : ℝ)) (√(26 / (10 * 12742) : ℝ)) d.D d.V d.P (√(tA 12742) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3652629 / 1000000000)) * (((2172213931 / 1000000000000000)) * ((3848697633 / 100000000000000000))) + ((1245695611 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12742) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((58981417 / 12500000000000000000) : ℝ) + ((1245695611 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12742

namespace BstLean.Part266.Row12742
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12742 163 ∧
    0 ≤ (tableEnvelope C).f1 12742 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12742 163 ∧
    0 ≤ (tableEnvelope C).w1 12742 163 ∧ 0 ≤ (tableEnvelope C).w2 12742 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12742 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12742 163 ∧ 0 ≤ d.f1 12742 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12742 163 ∧ 0 ≤ d.w1 12742 163 ∧ 0 ≤ d.w2 12742 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12742 ≤ 2 * (228 / 100 : ℝ) / 12742 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12742 ≤ 2 * (370 / 100 : ℝ) / 12742 := by
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
    (completeRAData (tableEnvelope C) 12742 163).locationBound 12742 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12742 163).energyBound 12742 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12742 163) (d.f1 12742 163) d.f2 ≤
      32 * (((2272515441 / 500000000000000000) : ℝ) + (12130393 / 8000000000000000) + (22777689 / 62500000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12742 163) (d.w1 12742 163)
      (d.w2 12742 163) ≤
      32 * (((1815130559 / 100000000000000000000) : ℝ) + (64571533 / 5000000000000000000) + (471856163 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12742 163) (d.f1 12742 163) d.f2 ≤
      ((2272515441 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2272515441 / 500000000000000000)) * ((12130393 / 8000000000000000)) * (126 / 100) +
      2 * (((12130393 / 8000000000000000)) ^ 2 + 2 * ((2272515441 / 500000000000000000)) * ((22777689 / 62500000000000000))) +
      6 * ((12130393 / 8000000000000000)) * ((22777689 / 62500000000000000)) * (126 / 100) + 8 * ((22777689 / 62500000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12742 163) (d.f1 12742 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12742 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12742 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12742 163) (d.f1 12742 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12742 163) (d.w1 12742 163) (d.w2 12742 163)
  have hwexpr0 : 0 ≤ d.w0 12742 163 + d.w1 12742 163 * √(π / 2) +
      2 * d.w2 12742 163 + energyR16 12742 *
      radiusPolynomialRoot16 (d.w0 12742 163) (d.w1 12742 163) (d.w2 12742 163) := by
    positivity
  constructor
  · change (12742 : ℝ) ^ 8 * (mA 12742 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12742 163) (d.f1 12742 163) d.f2 + locationR16 12742 *
        radiusPolynomialRoot16 (d.f0 12742 163) (d.f1 12742 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12742 : ℝ) ^ 8 * (mA 12742 : ℝ) ^ 8 *
        ((((2272515441 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2272515441 / 500000000000000000)) * ((12130393 / 8000000000000000)) * (126 / 100) +
          2 * (((12130393 / 8000000000000000)) ^ 2 + 2 * ((2272515441 / 500000000000000000)) * ((22777689 / 62500000000000000))) +
          6 * ((12130393 / 8000000000000000)) * ((22777689 / 62500000000000000)) * (126 / 100) + 8 * ((22777689 / 62500000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12742) *
          (32 * (((2272515441 / 500000000000000000) : ℝ) + (12130393 / 8000000000000000) + (22777689 / 62500000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12742 : ℝ) ^ 16 *
      (d.w0 12742 163 + d.w1 12742 163 * √(π / 2) + 2 * d.w2 12742 163 +
        energyR16 12742 * radiusPolynomialRoot16 (d.w0 12742 163) (d.w1 12742 163)
          (d.w2 12742 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12742 : ℝ) ^ 16 *
        (((1815130559 / 100000000000000000000) : ℝ) + ((64571533 / 5000000000000000000)) * (126 / 100) + 2 * ((471856163 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12742) *
          (32 * (((1815130559 / 100000000000000000000) : ℝ) + (64571533 / 5000000000000000000) + (471856163 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12742

/-! A coarse bound on the actual paper statistics constant at dimension 12743. -/
namespace BstLean.Part266.Row12743
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12741 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12741 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12741 128 ≤ (12995 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12995 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12743) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12743 : ℕ))
    (by norm_num : (12743 : ℕ) ≤ 16384)
  have ht : paperTail256 12743 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12743 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12743 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12743 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12743 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12743 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12741 128 * √(2 / (12743 : ℝ)) *
      (√(12743 : ℝ) + paperT0 12743 + paperTail256 12743) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12743 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12743 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12743 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12741 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12741 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12743 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12743

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12743
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12743 (61 / 100) 163 (17 / (100 * 12743)) (26 / (10 * 12743)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12743 (61 / 100) 163 (17 / (100 * 12743)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (235870127 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1480782423 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2489812441 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12743 / 12743 * (61 / 100)) ^ 4 * inverseRadius8 (12743 - 1) /
            envelopeGap 12743 (61 / 100) 163 (17 / (100 * 12743)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12743

namespace BstLean.Part266.Row12743
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12743 163 ≤ (90882761 / 20000000000000000)
  f1 : (tableEnvelope C).f1 12743 163 ≤ (75800069 / 50000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (364371493 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12743 163 ≤ (1814703009 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12743 163 ≤ (1291126521 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12743 163 ≤ (235872539 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (235870127 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (235870127 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1480782423 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2489812441 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1826243 / 500000000) : ℝ) ≤ √(17 / (100 * 12743) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12743) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (542989557 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38480935839 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12743) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12743) ≤ (110979641 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12743) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12743 * (163 : ℝ) ^ 2 + 26 / (10 * 12743) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12743) : ℝ)) (tA 12743 * 163 ^ 2 + 26 / (10 * 12743)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1826243 / 500000000))) * ((235870127 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1826243 / 500000000)) ^ 3) * ((1480782423 / 1000000000000000000000000))) + ((2489812441 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1826243 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12743) : ℝ)) d.D d.V d.P (√(tA 12743) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1826243 / 500000000)) ^ 2 * (((542989557 / 250000000000000)) * ((38480935839 / 1000000000000000000)))) + ((2489812441 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12743) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1826243 / 500000000)) * ((235870127 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12743) : ℝ)) (tA 12743 * 163 ^ 2 + 26 / (10 * 12743)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((235870127 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1826243 / 500000000)) ^ 2) * ((1480782423 / 1000000000000000000000000)) + ((2489812441 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12743) : ℝ)) (√(26 / (10 * 12743) : ℝ)) d.D d.V d.P (√(tA 12743) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1826243 / 500000000)) * (((542989557 / 250000000000000)) * ((38480935839 / 1000000000000000000))) + ((2489812441 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12743) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((235870127 / 50000000000000000000) : ℝ) + ((2489812441 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12743

namespace BstLean.Part266.Row12743
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12743 163 ∧
    0 ≤ (tableEnvelope C).f1 12743 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12743 163 ∧
    0 ≤ (tableEnvelope C).w1 12743 163 ∧ 0 ≤ (tableEnvelope C).w2 12743 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12743 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12743 163 ∧ 0 ≤ d.f1 12743 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12743 163 ∧ 0 ≤ d.w1 12743 163 ∧ 0 ≤ d.w2 12743 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12743 ≤ 2 * (228 / 100 : ℝ) / 12743 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12743 ≤ 2 * (370 / 100 : ℝ) / 12743 := by
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
    (completeRAData (tableEnvelope C) 12743 163).locationBound 12743 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12743 163).energyBound 12743 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12743 163) (d.f1 12743 163) d.f2 ≤
      32 * (((90882761 / 20000000000000000) : ℝ) + (75800069 / 50000000000000000) + (364371493 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12743 163) (d.w1 12743 163)
      (d.w2 12743 163) ≤
      32 * (((1814703009 / 100000000000000000000) : ℝ) + (1291126521 / 100000000000000000000) + (235872539 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12743 163) (d.f1 12743 163) d.f2 ≤
      ((90882761 / 20000000000000000) : ℝ) ^ 2 + 2 * ((90882761 / 20000000000000000)) * ((75800069 / 50000000000000000)) * (126 / 100) +
      2 * (((75800069 / 50000000000000000)) ^ 2 + 2 * ((90882761 / 20000000000000000)) * ((364371493 / 1000000000000000000))) +
      6 * ((75800069 / 50000000000000000)) * ((364371493 / 1000000000000000000)) * (126 / 100) + 8 * ((364371493 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12743 163) (d.f1 12743 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12743 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12743 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12743 163) (d.f1 12743 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12743 163) (d.w1 12743 163) (d.w2 12743 163)
  have hwexpr0 : 0 ≤ d.w0 12743 163 + d.w1 12743 163 * √(π / 2) +
      2 * d.w2 12743 163 + energyR16 12743 *
      radiusPolynomialRoot16 (d.w0 12743 163) (d.w1 12743 163) (d.w2 12743 163) := by
    positivity
  constructor
  · change (12743 : ℝ) ^ 8 * (mA 12743 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12743 163) (d.f1 12743 163) d.f2 + locationR16 12743 *
        radiusPolynomialRoot16 (d.f0 12743 163) (d.f1 12743 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12743 : ℝ) ^ 8 * (mA 12743 : ℝ) ^ 8 *
        ((((90882761 / 20000000000000000) : ℝ) ^ 2 + 2 * ((90882761 / 20000000000000000)) * ((75800069 / 50000000000000000)) * (126 / 100) +
          2 * (((75800069 / 50000000000000000)) ^ 2 + 2 * ((90882761 / 20000000000000000)) * ((364371493 / 1000000000000000000))) +
          6 * ((75800069 / 50000000000000000)) * ((364371493 / 1000000000000000000)) * (126 / 100) + 8 * ((364371493 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12743) *
          (32 * (((90882761 / 20000000000000000) : ℝ) + (75800069 / 50000000000000000) + (364371493 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12743 : ℝ) ^ 16 *
      (d.w0 12743 163 + d.w1 12743 163 * √(π / 2) + 2 * d.w2 12743 163 +
        energyR16 12743 * radiusPolynomialRoot16 (d.w0 12743 163) (d.w1 12743 163)
          (d.w2 12743 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12743 : ℝ) ^ 16 *
        (((1814703009 / 100000000000000000000) : ℝ) + ((1291126521 / 100000000000000000000)) * (126 / 100) + 2 * ((235872539 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12743) *
          (32 * (((1814703009 / 100000000000000000000) : ℝ) + (1291126521 / 100000000000000000000) + (235872539 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12743

/-! A coarse bound on the actual paper statistics constant at dimension 12744. -/
namespace BstLean.Part266.Row12744
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12742 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12742 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12742 128 ≤ (12996 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12996 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12744) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12744 : ℕ))
    (by norm_num : (12744 : ℕ) ≤ 16384)
  have ht : paperTail256 12744 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12744 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12744 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12744 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12744 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12744 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12742 128 * √(2 / (12744 : ℝ)) *
      (√(12744 : ℝ) + paperT0 12744 + paperTail256 12744) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12744 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12744 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12744 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12742 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12742 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12744 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12744

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12744
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12744 (61 / 100) 163 (17 / (100 * 12744)) (26 / (10 * 12744)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12744 (61 / 100) 163 (17 / (100 * 12744)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (471629207 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1480317681 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4976469573 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12744 / 12744 * (61 / 100)) ^ 4 * inverseRadius8 (12744 - 1) /
            envelopeGap 12744 (61 / 100) 163 (17 / (100 * 12744)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12744

namespace BstLean.Part266.Row12744
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12744 163 ≤ (2271622761 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12744 163 ≤ (151570373 / 100000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (364299983 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12744 163 ≤ (362855121 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12744 163 ≤ (1290822483 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12744 163 ≤ (117908507 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (471629207 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (471629207 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1480317681 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4976469573 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3652343 / 1000000000) : ℝ) ≤ √(17 / (100 * 12744) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12744) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (86868103 / 40000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9618724191 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12744) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12744) ≤ (110970933 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12744) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12744 * (163 : ℝ) ^ 2 + 26 / (10 * 12744) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12744) : ℝ)) (tA 12744 * 163 ^ 2 + 26 / (10 * 12744)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3652343 / 1000000000))) * ((471629207 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3652343 / 1000000000)) ^ 3) * ((1480317681 / 1000000000000000000000000))) + ((4976469573 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3652343 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12744) : ℝ)) d.D d.V d.P (√(tA 12744) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3652343 / 1000000000)) ^ 2 * (((86868103 / 40000000000000)) * ((9618724191 / 250000000000000000)))) + ((4976469573 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12744) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3652343 / 1000000000)) * ((471629207 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12744) : ℝ)) (tA 12744 * 163 ^ 2 + 26 / (10 * 12744)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((471629207 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3652343 / 1000000000)) ^ 2) * ((1480317681 / 1000000000000000000000000)) + ((4976469573 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12744) : ℝ)) (√(26 / (10 * 12744) : ℝ)) d.D d.V d.P (√(tA 12744) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3652343 / 1000000000)) * (((86868103 / 40000000000000)) * ((9618724191 / 250000000000000000))) + ((4976469573 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12744) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((471629207 / 100000000000000000000) : ℝ) + ((4976469573 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12744

namespace BstLean.Part266.Row12744
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12744 163 ∧
    0 ≤ (tableEnvelope C).f1 12744 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12744 163 ∧
    0 ≤ (tableEnvelope C).w1 12744 163 ∧ 0 ≤ (tableEnvelope C).w2 12744 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12744 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12744 163 ∧ 0 ≤ d.f1 12744 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12744 163 ∧ 0 ≤ d.w1 12744 163 ∧ 0 ≤ d.w2 12744 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12744 ≤ 2 * (228 / 100 : ℝ) / 12744 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12744 ≤ 2 * (370 / 100 : ℝ) / 12744 := by
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
    (completeRAData (tableEnvelope C) 12744 163).locationBound 12744 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12744 163).energyBound 12744 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12744 163) (d.f1 12744 163) d.f2 ≤
      32 * (((2271622761 / 500000000000000000) : ℝ) + (151570373 / 100000000000000000) + (364299983 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12744 163) (d.w1 12744 163)
      (d.w2 12744 163) ≤
      32 * (((362855121 / 20000000000000000000) : ℝ) + (1290822483 / 100000000000000000000) + (117908507 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12744 163) (d.f1 12744 163) d.f2 ≤
      ((2271622761 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2271622761 / 500000000000000000)) * ((151570373 / 100000000000000000)) * (126 / 100) +
      2 * (((151570373 / 100000000000000000)) ^ 2 + 2 * ((2271622761 / 500000000000000000)) * ((364299983 / 1000000000000000000))) +
      6 * ((151570373 / 100000000000000000)) * ((364299983 / 1000000000000000000)) * (126 / 100) + 8 * ((364299983 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12744 163) (d.f1 12744 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12744 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12744 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12744 163) (d.f1 12744 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12744 163) (d.w1 12744 163) (d.w2 12744 163)
  have hwexpr0 : 0 ≤ d.w0 12744 163 + d.w1 12744 163 * √(π / 2) +
      2 * d.w2 12744 163 + energyR16 12744 *
      radiusPolynomialRoot16 (d.w0 12744 163) (d.w1 12744 163) (d.w2 12744 163) := by
    positivity
  constructor
  · change (12744 : ℝ) ^ 8 * (mA 12744 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12744 163) (d.f1 12744 163) d.f2 + locationR16 12744 *
        radiusPolynomialRoot16 (d.f0 12744 163) (d.f1 12744 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12744 : ℝ) ^ 8 * (mA 12744 : ℝ) ^ 8 *
        ((((2271622761 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2271622761 / 500000000000000000)) * ((151570373 / 100000000000000000)) * (126 / 100) +
          2 * (((151570373 / 100000000000000000)) ^ 2 + 2 * ((2271622761 / 500000000000000000)) * ((364299983 / 1000000000000000000))) +
          6 * ((151570373 / 100000000000000000)) * ((364299983 / 1000000000000000000)) * (126 / 100) + 8 * ((364299983 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12744) *
          (32 * (((2271622761 / 500000000000000000) : ℝ) + (151570373 / 100000000000000000) + (364299983 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12744 : ℝ) ^ 16 *
      (d.w0 12744 163 + d.w1 12744 163 * √(π / 2) + 2 * d.w2 12744 163 +
        energyR16 12744 * radiusPolynomialRoot16 (d.w0 12744 163) (d.w1 12744 163)
          (d.w2 12744 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12744 : ℝ) ^ 16 *
        (((362855121 / 20000000000000000000) : ℝ) + ((1290822483 / 100000000000000000000)) * (126 / 100) + 2 * ((117908507 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12744) *
          (32 * (((362855121 / 20000000000000000000) : ℝ) + (1290822483 / 100000000000000000000) + (117908507 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12744

/-! A coarse bound on the actual paper statistics constant at dimension 12745. -/
namespace BstLean.Part266.Row12745
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12743 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12743 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12743 128 ≤ (12997 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12997 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12745) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12745 : ℕ))
    (by norm_num : (12745 : ℕ) ≤ 16384)
  have ht : paperTail256 12745 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12745 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12745 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12745 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12745 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12745 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12743 128 * √(2 / (12745 : ℝ)) *
      (√(12745 : ℝ) + paperT0 12745 + paperTail256 12745) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12745 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12745 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12745 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12743 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12743 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12745 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12745

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12745
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12745 (61 / 100) 163 (17 / (100 * 12745)) (26 / (10 * 12745)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12745 (61 / 100) 163 (17 / (100 * 12745)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (235759097 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (739926561 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1243329129 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12745 / 12745 * (61 / 100)) ^ 4 * inverseRadius8 (12745 - 1) /
            envelopeGap 12745 (61 / 100) 163 (17 / (100 * 12745)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12745

namespace BstLean.Part266.Row12745
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12745 163 ≤ (4542356893 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12745 163 ≤ (378851751 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (182114297 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12745 163 ≤ (1813849083 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12745 163 ≤ (1290518899 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12745 163 ≤ (117880753 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (235759097 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (235759097 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (739926561 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1243329129 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3652199 / 1000000000) : ℝ) ≤ √(17 / (100 * 12745) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12745) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (217144697 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38468859121 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12745) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12745) ≤ (55481113 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12745) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12745 * (163 : ℝ) ^ 2 + 26 / (10 * 12745) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12745) : ℝ)) (tA 12745 * 163 ^ 2 + 26 / (10 * 12745)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3652199 / 1000000000))) * ((235759097 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3652199 / 1000000000)) ^ 3) * ((739926561 / 500000000000000000000000))) + ((1243329129 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3652199 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12745) : ℝ)) d.D d.V d.P (√(tA 12745) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3652199 / 1000000000)) ^ 2 * (((217144697 / 100000000000000)) * ((38468859121 / 1000000000000000000)))) + ((1243329129 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12745) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3652199 / 1000000000)) * ((235759097 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12745) : ℝ)) (tA 12745 * 163 ^ 2 + 26 / (10 * 12745)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((235759097 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3652199 / 1000000000)) ^ 2) * ((739926561 / 500000000000000000000000)) + ((1243329129 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12745) : ℝ)) (√(26 / (10 * 12745) : ℝ)) d.D d.V d.P (√(tA 12745) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3652199 / 1000000000)) * (((217144697 / 100000000000000)) * ((38468859121 / 1000000000000000000))) + ((1243329129 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12745) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((235759097 / 50000000000000000000) : ℝ) + ((1243329129 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12745

namespace BstLean.Part266.Row12745
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12745 163 ∧
    0 ≤ (tableEnvelope C).f1 12745 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12745 163 ∧
    0 ≤ (tableEnvelope C).w1 12745 163 ∧ 0 ≤ (tableEnvelope C).w2 12745 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12745 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12745 163 ∧ 0 ≤ d.f1 12745 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12745 163 ∧ 0 ≤ d.w1 12745 163 ∧ 0 ≤ d.w2 12745 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12745 ≤ 2 * (228 / 100 : ℝ) / 12745 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12745 ≤ 2 * (370 / 100 : ℝ) / 12745 := by
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
    (completeRAData (tableEnvelope C) 12745 163).locationBound 12745 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12745 163).energyBound 12745 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12745 163) (d.f1 12745 163) d.f2 ≤
      32 * (((4542356893 / 1000000000000000000) : ℝ) + (378851751 / 250000000000000000) + (182114297 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12745 163) (d.w1 12745 163)
      (d.w2 12745 163) ≤
      32 * (((1813849083 / 100000000000000000000) : ℝ) + (1290518899 / 100000000000000000000) + (117880753 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12745 163) (d.f1 12745 163) d.f2 ≤
      ((4542356893 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4542356893 / 1000000000000000000)) * ((378851751 / 250000000000000000)) * (126 / 100) +
      2 * (((378851751 / 250000000000000000)) ^ 2 + 2 * ((4542356893 / 1000000000000000000)) * ((182114297 / 500000000000000000))) +
      6 * ((378851751 / 250000000000000000)) * ((182114297 / 500000000000000000)) * (126 / 100) + 8 * ((182114297 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12745 163) (d.f1 12745 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12745 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12745 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12745 163) (d.f1 12745 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12745 163) (d.w1 12745 163) (d.w2 12745 163)
  have hwexpr0 : 0 ≤ d.w0 12745 163 + d.w1 12745 163 * √(π / 2) +
      2 * d.w2 12745 163 + energyR16 12745 *
      radiusPolynomialRoot16 (d.w0 12745 163) (d.w1 12745 163) (d.w2 12745 163) := by
    positivity
  constructor
  · change (12745 : ℝ) ^ 8 * (mA 12745 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12745 163) (d.f1 12745 163) d.f2 + locationR16 12745 *
        radiusPolynomialRoot16 (d.f0 12745 163) (d.f1 12745 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12745 : ℝ) ^ 8 * (mA 12745 : ℝ) ^ 8 *
        ((((4542356893 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4542356893 / 1000000000000000000)) * ((378851751 / 250000000000000000)) * (126 / 100) +
          2 * (((378851751 / 250000000000000000)) ^ 2 + 2 * ((4542356893 / 1000000000000000000)) * ((182114297 / 500000000000000000))) +
          6 * ((378851751 / 250000000000000000)) * ((182114297 / 500000000000000000)) * (126 / 100) + 8 * ((182114297 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12745) *
          (32 * (((4542356893 / 1000000000000000000) : ℝ) + (378851751 / 250000000000000000) + (182114297 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12745 : ℝ) ^ 16 *
      (d.w0 12745 163 + d.w1 12745 163 * √(π / 2) + 2 * d.w2 12745 163 +
        energyR16 12745 * radiusPolynomialRoot16 (d.w0 12745 163) (d.w1 12745 163)
          (d.w2 12745 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12745 : ℝ) ^ 16 *
        (((1813849083 / 100000000000000000000) : ℝ) + ((1290518899 / 100000000000000000000)) * (126 / 100) + 2 * ((117880753 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12745) *
          (32 * (((1813849083 / 100000000000000000000) : ℝ) + (1290518899 / 100000000000000000000) + (117880753 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12745

/-! A coarse bound on the actual paper statistics constant at dimension 12746. -/
namespace BstLean.Part266.Row12746
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12744 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12744 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12744 128 ≤ (12998 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12998 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12746) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12746 : ℕ))
    (by norm_num : (12746 : ℕ) ≤ 16384)
  have ht : paperTail256 12746 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12746 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12746 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12746 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12746 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12746 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12744 128 * √(2 / (12746 : ℝ)) *
      (√(12746 : ℝ) + paperT0 12746 + paperTail256 12746) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12746 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12746 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12746 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12744 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12744 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12746 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12746

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12746
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12746 (61 / 100) 163 (17 / (100 * 12746)) (26 / (10 * 12746)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12746 (61 / 100) 163 (17 / (100 * 12746)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (471407217 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (295877749 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4970165709 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12746 / 12746 * (61 / 100)) ^ 4 * inverseRadius8 (12746 - 1) /
            envelopeGap 12746 (61 / 100) 163 (17 / (100 * 12746)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12746

namespace BstLean.Part266.Row12746
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12746 163 ≤ (4541464977 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12746 163 ≤ (1515109547 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (364157127 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12746 163 ≤ (453355493 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12746 163 ≤ (258043013 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12746 163 ≤ (7365813 / 1562500000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (471407217 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (471407217 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (295877749 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4970165709 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((456507 / 125000000) : ℝ) ≤ √(17 / (100 * 12746) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12746) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1085595709 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7692564579 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12746) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12746) ≤ (1386919 / 12500000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12746) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12746 * (163 : ℝ) ^ 2 + 26 / (10 * 12746) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12746) : ℝ)) (tA 12746 * 163 ^ 2 + 26 / (10 * 12746)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((456507 / 125000000))) * ((471407217 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((456507 / 125000000)) ^ 3) * ((295877749 / 200000000000000000000000))) + ((4970165709 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((456507 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12746) : ℝ)) d.D d.V d.P (√(tA 12746) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((456507 / 125000000)) ^ 2 * (((1085595709 / 500000000000000)) * ((7692564579 / 200000000000000000)))) + ((4970165709 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12746) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((456507 / 125000000)) * ((471407217 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12746) : ℝ)) (tA 12746 * 163 ^ 2 + 26 / (10 * 12746)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((471407217 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((456507 / 125000000)) ^ 2) * ((295877749 / 200000000000000000000000)) + ((4970165709 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12746) : ℝ)) (√(26 / (10 * 12746) : ℝ)) d.D d.V d.P (√(tA 12746) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((456507 / 125000000)) * (((1085595709 / 500000000000000)) * ((7692564579 / 200000000000000000))) + ((4970165709 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12746) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((471407217 / 100000000000000000000) : ℝ) + ((4970165709 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12746

namespace BstLean.Part266.Row12746
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12746 163 ∧
    0 ≤ (tableEnvelope C).f1 12746 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12746 163 ∧
    0 ≤ (tableEnvelope C).w1 12746 163 ∧ 0 ≤ (tableEnvelope C).w2 12746 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12746 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12746 163 ∧ 0 ≤ d.f1 12746 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12746 163 ∧ 0 ≤ d.w1 12746 163 ∧ 0 ≤ d.w2 12746 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12746 ≤ 2 * (228 / 100 : ℝ) / 12746 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12746 ≤ 2 * (370 / 100 : ℝ) / 12746 := by
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
    (completeRAData (tableEnvelope C) 12746 163).locationBound 12746 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12746 163).energyBound 12746 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12746 163) (d.f1 12746 163) d.f2 ≤
      32 * (((4541464977 / 1000000000000000000) : ℝ) + (1515109547 / 1000000000000000000) + (364157127 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12746 163) (d.w1 12746 163)
      (d.w2 12746 163) ≤
      32 * (((453355493 / 25000000000000000000) : ℝ) + (258043013 / 20000000000000000000) + (7365813 / 1562500000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12746 163) (d.f1 12746 163) d.f2 ≤
      ((4541464977 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4541464977 / 1000000000000000000)) * ((1515109547 / 1000000000000000000)) * (126 / 100) +
      2 * (((1515109547 / 1000000000000000000)) ^ 2 + 2 * ((4541464977 / 1000000000000000000)) * ((364157127 / 1000000000000000000))) +
      6 * ((1515109547 / 1000000000000000000)) * ((364157127 / 1000000000000000000)) * (126 / 100) + 8 * ((364157127 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12746 163) (d.f1 12746 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12746 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12746 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12746 163) (d.f1 12746 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12746 163) (d.w1 12746 163) (d.w2 12746 163)
  have hwexpr0 : 0 ≤ d.w0 12746 163 + d.w1 12746 163 * √(π / 2) +
      2 * d.w2 12746 163 + energyR16 12746 *
      radiusPolynomialRoot16 (d.w0 12746 163) (d.w1 12746 163) (d.w2 12746 163) := by
    positivity
  constructor
  · change (12746 : ℝ) ^ 8 * (mA 12746 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12746 163) (d.f1 12746 163) d.f2 + locationR16 12746 *
        radiusPolynomialRoot16 (d.f0 12746 163) (d.f1 12746 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12746 : ℝ) ^ 8 * (mA 12746 : ℝ) ^ 8 *
        ((((4541464977 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4541464977 / 1000000000000000000)) * ((1515109547 / 1000000000000000000)) * (126 / 100) +
          2 * (((1515109547 / 1000000000000000000)) ^ 2 + 2 * ((4541464977 / 1000000000000000000)) * ((364157127 / 1000000000000000000))) +
          6 * ((1515109547 / 1000000000000000000)) * ((364157127 / 1000000000000000000)) * (126 / 100) + 8 * ((364157127 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12746) *
          (32 * (((4541464977 / 1000000000000000000) : ℝ) + (1515109547 / 1000000000000000000) + (364157127 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12746 : ℝ) ^ 16 *
      (d.w0 12746 163 + d.w1 12746 163 * √(π / 2) + 2 * d.w2 12746 163 +
        energyR16 12746 * radiusPolynomialRoot16 (d.w0 12746 163) (d.w1 12746 163)
          (d.w2 12746 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12746 : ℝ) ^ 16 *
        (((453355493 / 25000000000000000000) : ℝ) + ((258043013 / 20000000000000000000)) * (126 / 100) + 2 * ((7365813 / 1562500000000000000)) +
          (2 * (370 / 100 : ℝ) / 12746) *
          (32 * (((453355493 / 25000000000000000000) : ℝ) + (258043013 / 20000000000000000000) + (7365813 / 1562500000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12746

/-! A coarse bound on the actual paper statistics constant at dimension 12747. -/
namespace BstLean.Part266.Row12747
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12745 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12745 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12745 128 ≤ (12999 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12999 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12747) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12747 : ℕ))
    (by norm_num : (12747 : ℕ) ≤ 16384)
  have ht : paperTail256 12747 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12747 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12747 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12747 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12747 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12747 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12745 128 * √(2 / (12747 : ℝ)) *
      (√(12747 : ℝ) + paperT0 12747 + paperTail256 12747) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12747 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12747 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12747 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12745 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12745 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12747 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12747

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12747
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12747 (61 / 100) 163 (17 / (100 * 12747)) (26 / (10 * 12747)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12747 (61 / 100) 163 (17 / (100 * 12747)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (235648137 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1478924551 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4967017149 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12747 / 12747 * (61 / 100)) ^ 4 * inverseRadius8 (12747 - 1) /
            envelopeGap 12747 (61 / 100) 163 (17 / (100 * 12747)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12747

namespace BstLean.Part266.Row12747
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12747 163 ≤ (454057337 / 100000000000000000)
  f1 : (tableEnvelope C).f1 12747 163 ≤ (189351523 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (364085681 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12747 163 ≤ (28328047 / 1562500000000000000)
  w1 : (tableEnvelope C).w1 12747 163 ≤ (1289911331 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12747 163 ≤ (235650543 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (235648137 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (235648137 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1478924551 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4967017149 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3651913 / 1000000000) : ℝ) ≤ √(17 / (100 * 12747) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12747) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1085467957 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38456788101 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12747) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12747) ≤ (6934051 / 62500000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12747) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12747 * (163 : ℝ) ^ 2 + 26 / (10 * 12747) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12747) : ℝ)) (tA 12747 * 163 ^ 2 + 26 / (10 * 12747)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3651913 / 1000000000))) * ((235648137 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3651913 / 1000000000)) ^ 3) * ((1478924551 / 1000000000000000000000000))) + ((4967017149 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3651913 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12747) : ℝ)) d.D d.V d.P (√(tA 12747) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3651913 / 1000000000)) ^ 2 * (((1085467957 / 500000000000000)) * ((38456788101 / 1000000000000000000)))) + ((4967017149 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12747) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3651913 / 1000000000)) * ((235648137 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12747) : ℝ)) (tA 12747 * 163 ^ 2 + 26 / (10 * 12747)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((235648137 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3651913 / 1000000000)) ^ 2) * ((1478924551 / 1000000000000000000000000)) + ((4967017149 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12747) : ℝ)) (√(26 / (10 * 12747) : ℝ)) d.D d.V d.P (√(tA 12747) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3651913 / 1000000000)) * (((1085467957 / 500000000000000)) * ((38456788101 / 1000000000000000000))) + ((4967017149 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12747) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((235648137 / 50000000000000000000) : ℝ) + ((4967017149 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12747

namespace BstLean.Part266.Row12747
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12747 163 ∧
    0 ≤ (tableEnvelope C).f1 12747 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12747 163 ∧
    0 ≤ (tableEnvelope C).w1 12747 163 ∧ 0 ≤ (tableEnvelope C).w2 12747 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12747 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12747 163 ∧ 0 ≤ d.f1 12747 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12747 163 ∧ 0 ≤ d.w1 12747 163 ∧ 0 ≤ d.w2 12747 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12747 ≤ 2 * (228 / 100 : ℝ) / 12747 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12747 ≤ 2 * (370 / 100 : ℝ) / 12747 := by
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
    (completeRAData (tableEnvelope C) 12747 163).locationBound 12747 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12747 163).energyBound 12747 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12747 163) (d.f1 12747 163) d.f2 ≤
      32 * (((454057337 / 100000000000000000) : ℝ) + (189351523 / 125000000000000000) + (364085681 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12747 163) (d.w1 12747 163)
      (d.w2 12747 163) ≤
      32 * (((28328047 / 1562500000000000000) : ℝ) + (1289911331 / 100000000000000000000) + (235650543 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12747 163) (d.f1 12747 163) d.f2 ≤
      ((454057337 / 100000000000000000) : ℝ) ^ 2 + 2 * ((454057337 / 100000000000000000)) * ((189351523 / 125000000000000000)) * (126 / 100) +
      2 * (((189351523 / 125000000000000000)) ^ 2 + 2 * ((454057337 / 100000000000000000)) * ((364085681 / 1000000000000000000))) +
      6 * ((189351523 / 125000000000000000)) * ((364085681 / 1000000000000000000)) * (126 / 100) + 8 * ((364085681 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12747 163) (d.f1 12747 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12747 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12747 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12747 163) (d.f1 12747 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12747 163) (d.w1 12747 163) (d.w2 12747 163)
  have hwexpr0 : 0 ≤ d.w0 12747 163 + d.w1 12747 163 * √(π / 2) +
      2 * d.w2 12747 163 + energyR16 12747 *
      radiusPolynomialRoot16 (d.w0 12747 163) (d.w1 12747 163) (d.w2 12747 163) := by
    positivity
  constructor
  · change (12747 : ℝ) ^ 8 * (mA 12747 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12747 163) (d.f1 12747 163) d.f2 + locationR16 12747 *
        radiusPolynomialRoot16 (d.f0 12747 163) (d.f1 12747 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12747 : ℝ) ^ 8 * (mA 12747 : ℝ) ^ 8 *
        ((((454057337 / 100000000000000000) : ℝ) ^ 2 + 2 * ((454057337 / 100000000000000000)) * ((189351523 / 125000000000000000)) * (126 / 100) +
          2 * (((189351523 / 125000000000000000)) ^ 2 + 2 * ((454057337 / 100000000000000000)) * ((364085681 / 1000000000000000000))) +
          6 * ((189351523 / 125000000000000000)) * ((364085681 / 1000000000000000000)) * (126 / 100) + 8 * ((364085681 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12747) *
          (32 * (((454057337 / 100000000000000000) : ℝ) + (189351523 / 125000000000000000) + (364085681 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12747 : ℝ) ^ 16 *
      (d.w0 12747 163 + d.w1 12747 163 * √(π / 2) + 2 * d.w2 12747 163 +
        energyR16 12747 * radiusPolynomialRoot16 (d.w0 12747 163) (d.w1 12747 163)
          (d.w2 12747 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12747 : ℝ) ^ 16 *
        (((28328047 / 1562500000000000000) : ℝ) + ((1289911331 / 100000000000000000000)) * (126 / 100) + 2 * ((235650543 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12747) *
          (32 * (((28328047 / 1562500000000000000) : ℝ) + (1289911331 / 100000000000000000000) + (235650543 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12747

/-! A coarse bound on the actual paper statistics constant at dimension 12748. -/
namespace BstLean.Part266.Row12748
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12746 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12746 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12746 128 ≤ (13000 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13000 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12748) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12748 : ℕ))
    (by norm_num : (12748 : ℕ) ≤ 16384)
  have ht : paperTail256 12748 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12748 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12748 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12748 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12748 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12748 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12746 128 * √(2 / (12748 : ℝ)) *
      (√(12748 : ℝ) + paperT0 12748 + paperTail256 12748) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12748 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12748 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12748 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12746 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12746 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12748 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12748

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12748
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12748 (61 / 100) 163 (17 / (100 * 12748)) (26 / (10 * 12748)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12748 (61 / 100) 163 (17 / (100 * 12748)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (471185367 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (739230269 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (992774167 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12748 / 12748 * (61 / 100)) ^ 4 * inverseRadius8 (12748 - 1) /
            envelopeGap 12748 (61 / 100) 163 (17 / (100 * 12748)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12748

namespace BstLean.Part266.Row12748
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12748 163 ≤ (907936413 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12748 163 ≤ (757257459 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (364014257 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12748 163 ≤ (1812568191 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12748 163 ≤ (1289607699 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12748 163 ≤ (14724693 / 3125000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (471185367 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (471185367 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (739230269 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (992774167 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((365177 / 100000000) : ℝ) ≤ √(17 / (100 * 12748) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12748) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2170680463 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19225377357 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12748) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12748) ≤ (110936113 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12748) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12748 * (163 : ℝ) ^ 2 + 26 / (10 * 12748) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12748) : ℝ)) (tA 12748 * 163 ^ 2 + 26 / (10 * 12748)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((365177 / 100000000))) * ((471185367 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((365177 / 100000000)) ^ 3) * ((739230269 / 500000000000000000000000))) + ((992774167 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((365177 / 100000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12748) : ℝ)) d.D d.V d.P (√(tA 12748) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((365177 / 100000000)) ^ 2 * (((2170680463 / 1000000000000000)) * ((19225377357 / 500000000000000000)))) + ((992774167 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12748) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((365177 / 100000000)) * ((471185367 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12748) : ℝ)) (tA 12748 * 163 ^ 2 + 26 / (10 * 12748)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((471185367 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((365177 / 100000000)) ^ 2) * ((739230269 / 500000000000000000000000)) + ((992774167 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12748) : ℝ)) (√(26 / (10 * 12748) : ℝ)) d.D d.V d.P (√(tA 12748) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((365177 / 100000000)) * (((2170680463 / 1000000000000000)) * ((19225377357 / 500000000000000000))) + ((992774167 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12748) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((471185367 / 100000000000000000000) : ℝ) + ((992774167 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12748

namespace BstLean.Part266.Row12748
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12748 163 ∧
    0 ≤ (tableEnvelope C).f1 12748 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12748 163 ∧
    0 ≤ (tableEnvelope C).w1 12748 163 ∧ 0 ≤ (tableEnvelope C).w2 12748 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12748 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12748 163 ∧ 0 ≤ d.f1 12748 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12748 163 ∧ 0 ≤ d.w1 12748 163 ∧ 0 ≤ d.w2 12748 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12748 ≤ 2 * (228 / 100 : ℝ) / 12748 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12748 ≤ 2 * (370 / 100 : ℝ) / 12748 := by
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
    (completeRAData (tableEnvelope C) 12748 163).locationBound 12748 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12748 163).energyBound 12748 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12748 163) (d.f1 12748 163) d.f2 ≤
      32 * (((907936413 / 200000000000000000) : ℝ) + (757257459 / 500000000000000000) + (364014257 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12748 163) (d.w1 12748 163)
      (d.w2 12748 163) ≤
      32 * (((1812568191 / 100000000000000000000) : ℝ) + (1289607699 / 100000000000000000000) + (14724693 / 3125000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12748 163) (d.f1 12748 163) d.f2 ≤
      ((907936413 / 200000000000000000) : ℝ) ^ 2 + 2 * ((907936413 / 200000000000000000)) * ((757257459 / 500000000000000000)) * (126 / 100) +
      2 * (((757257459 / 500000000000000000)) ^ 2 + 2 * ((907936413 / 200000000000000000)) * ((364014257 / 1000000000000000000))) +
      6 * ((757257459 / 500000000000000000)) * ((364014257 / 1000000000000000000)) * (126 / 100) + 8 * ((364014257 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12748 163) (d.f1 12748 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12748 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12748 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12748 163) (d.f1 12748 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12748 163) (d.w1 12748 163) (d.w2 12748 163)
  have hwexpr0 : 0 ≤ d.w0 12748 163 + d.w1 12748 163 * √(π / 2) +
      2 * d.w2 12748 163 + energyR16 12748 *
      radiusPolynomialRoot16 (d.w0 12748 163) (d.w1 12748 163) (d.w2 12748 163) := by
    positivity
  constructor
  · change (12748 : ℝ) ^ 8 * (mA 12748 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12748 163) (d.f1 12748 163) d.f2 + locationR16 12748 *
        radiusPolynomialRoot16 (d.f0 12748 163) (d.f1 12748 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12748 : ℝ) ^ 8 * (mA 12748 : ℝ) ^ 8 *
        ((((907936413 / 200000000000000000) : ℝ) ^ 2 + 2 * ((907936413 / 200000000000000000)) * ((757257459 / 500000000000000000)) * (126 / 100) +
          2 * (((757257459 / 500000000000000000)) ^ 2 + 2 * ((907936413 / 200000000000000000)) * ((364014257 / 1000000000000000000))) +
          6 * ((757257459 / 500000000000000000)) * ((364014257 / 1000000000000000000)) * (126 / 100) + 8 * ((364014257 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12748) *
          (32 * (((907936413 / 200000000000000000) : ℝ) + (757257459 / 500000000000000000) + (364014257 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12748 : ℝ) ^ 16 *
      (d.w0 12748 163 + d.w1 12748 163 * √(π / 2) + 2 * d.w2 12748 163 +
        energyR16 12748 * radiusPolynomialRoot16 (d.w0 12748 163) (d.w1 12748 163)
          (d.w2 12748 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12748 : ℝ) ^ 16 *
        (((1812568191 / 100000000000000000000) : ℝ) + ((1289607699 / 100000000000000000000)) * (126 / 100) + 2 * ((14724693 / 3125000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12748) *
          (32 * (((1812568191 / 100000000000000000000) : ℝ) + (1289607699 / 100000000000000000000) + (14724693 / 3125000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12748

/-! A coarse bound on the actual paper statistics constant at dimension 12749. -/
namespace BstLean.Part266.Row12749
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12747 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12747 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12747 128 ≤ (13001 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13001 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12749) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12749 : ℕ))
    (by norm_num : (12749 : ℕ) ≤ 16384)
  have ht : paperTail256 12749 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12749 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12749 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12749 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12749 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12749 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12747 128 * √(2 / (12749 : ℝ)) *
      (√(12749 : ℝ) + paperT0 12749 + paperTail256 12749) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12749 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12749 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12749 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12747 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12747 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12749 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12749

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12749
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12749 (61 / 100) 163 (17 / (100 * 12749)) (26 / (10 * 12749)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12749 (61 / 100) 163 (17 / (100 * 12749)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (235537247 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1477996707 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (992145353 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12749 / 12749 * (61 / 100)) ^ 4 * inverseRadius8 (12749 - 1) /
            envelopeGap 12749 (61 / 100) 163 (17 / (100 * 12749)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12749

namespace BstLean.Part266.Row12749
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12749 163 ≤ (4538794653 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12749 163 ≤ (60568743 / 40000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (181971477 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12749 163 ≤ (906071127 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12749 163 ≤ (1289304521 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12749 163 ≤ (4710793 / 1000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (235537247 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (235537247 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1477996707 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (992145353 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1825813 / 500000000) : ℝ) ≤ √(17 / (100 * 12749) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12749) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (108521253 / 50000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19222361373 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12749) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12749) ≤ (110927411 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12749) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12749 * (163 : ℝ) ^ 2 + 26 / (10 * 12749) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12749) : ℝ)) (tA 12749 * 163 ^ 2 + 26 / (10 * 12749)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1825813 / 500000000))) * ((235537247 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1825813 / 500000000)) ^ 3) * ((1477996707 / 1000000000000000000000000))) + ((992145353 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1825813 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12749) : ℝ)) d.D d.V d.P (√(tA 12749) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1825813 / 500000000)) ^ 2 * (((108521253 / 50000000000000)) * ((19222361373 / 500000000000000000)))) + ((992145353 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12749) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1825813 / 500000000)) * ((235537247 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12749) : ℝ)) (tA 12749 * 163 ^ 2 + 26 / (10 * 12749)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((235537247 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1825813 / 500000000)) ^ 2) * ((1477996707 / 1000000000000000000000000)) + ((992145353 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12749) : ℝ)) (√(26 / (10 * 12749) : ℝ)) d.D d.V d.P (√(tA 12749) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1825813 / 500000000)) * (((108521253 / 50000000000000)) * ((19222361373 / 500000000000000000))) + ((992145353 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12749) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((235537247 / 50000000000000000000) : ℝ) + ((992145353 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12749

namespace BstLean.Part266.Row12749
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12749 163 ∧
    0 ≤ (tableEnvelope C).f1 12749 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12749 163 ∧
    0 ≤ (tableEnvelope C).w1 12749 163 ∧ 0 ≤ (tableEnvelope C).w2 12749 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12749 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12749 163 ∧ 0 ≤ d.f1 12749 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12749 163 ∧ 0 ≤ d.w1 12749 163 ∧ 0 ≤ d.w2 12749 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12749 ≤ 2 * (228 / 100 : ℝ) / 12749 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12749 ≤ 2 * (370 / 100 : ℝ) / 12749 := by
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
    (completeRAData (tableEnvelope C) 12749 163).locationBound 12749 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12749 163).energyBound 12749 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12749 163) (d.f1 12749 163) d.f2 ≤
      32 * (((4538794653 / 1000000000000000000) : ℝ) + (60568743 / 40000000000000000) + (181971477 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12749 163) (d.w1 12749 163)
      (d.w2 12749 163) ≤
      32 * (((906071127 / 50000000000000000000) : ℝ) + (1289304521 / 100000000000000000000) + (4710793 / 1000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12749 163) (d.f1 12749 163) d.f2 ≤
      ((4538794653 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4538794653 / 1000000000000000000)) * ((60568743 / 40000000000000000)) * (126 / 100) +
      2 * (((60568743 / 40000000000000000)) ^ 2 + 2 * ((4538794653 / 1000000000000000000)) * ((181971477 / 500000000000000000))) +
      6 * ((60568743 / 40000000000000000)) * ((181971477 / 500000000000000000)) * (126 / 100) + 8 * ((181971477 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12749 163) (d.f1 12749 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12749 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12749 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12749 163) (d.f1 12749 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12749 163) (d.w1 12749 163) (d.w2 12749 163)
  have hwexpr0 : 0 ≤ d.w0 12749 163 + d.w1 12749 163 * √(π / 2) +
      2 * d.w2 12749 163 + energyR16 12749 *
      radiusPolynomialRoot16 (d.w0 12749 163) (d.w1 12749 163) (d.w2 12749 163) := by
    positivity
  constructor
  · change (12749 : ℝ) ^ 8 * (mA 12749 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12749 163) (d.f1 12749 163) d.f2 + locationR16 12749 *
        radiusPolynomialRoot16 (d.f0 12749 163) (d.f1 12749 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12749 : ℝ) ^ 8 * (mA 12749 : ℝ) ^ 8 *
        ((((4538794653 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4538794653 / 1000000000000000000)) * ((60568743 / 40000000000000000)) * (126 / 100) +
          2 * (((60568743 / 40000000000000000)) ^ 2 + 2 * ((4538794653 / 1000000000000000000)) * ((181971477 / 500000000000000000))) +
          6 * ((60568743 / 40000000000000000)) * ((181971477 / 500000000000000000)) * (126 / 100) + 8 * ((181971477 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12749) *
          (32 * (((4538794653 / 1000000000000000000) : ℝ) + (60568743 / 40000000000000000) + (181971477 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12749 : ℝ) ^ 16 *
      (d.w0 12749 163 + d.w1 12749 163 * √(π / 2) + 2 * d.w2 12749 163 +
        energyR16 12749 * radiusPolynomialRoot16 (d.w0 12749 163) (d.w1 12749 163)
          (d.w2 12749 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12749 : ℝ) ^ 16 *
        (((906071127 / 50000000000000000000) : ℝ) + ((1289304521 / 100000000000000000000)) * (126 / 100) + 2 * ((4710793 / 1000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12749) *
          (32 * (((906071127 / 50000000000000000000) : ℝ) + (1289304521 / 100000000000000000000) + (4710793 / 1000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12749
