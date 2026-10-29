import BstLean.Part266Shard3Step4


/-! A coarse bound on the actual paper statistics constant at dimension 12425. -/
namespace BstLean.Part266.Row12425
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12423 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12423 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12423 128 ≤ (12677 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12677 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12425) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12425 : ℕ))
    (by norm_num : (12425 : ℕ) ≤ 16384)
  have ht : paperTail256 12425 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12425 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12425 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12425 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12425 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12425 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12423 128 * √(2 / (12425 : ℝ)) *
      (√(12425 : ℝ) + paperT0 12425 + paperTail256 12425) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12425 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12425 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12425 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12423 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12423 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12425 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12425

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12425
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12425 (61 / 100) 161 (17 / (100 * 12425)) (26 / (10 * 12425)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12425 (61 / 100) 161 (17 / (100 * 12425)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (508897759 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (409575667 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1525419871 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12425 / 12425 * (61 / 100)) ^ 4 * inverseRadius8 (12425 - 1) /
            envelopeGap 12425 (61 / 100) 161 (17 / (100 * 12425)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12425

namespace BstLean.Part266.Row12425
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12425 161 ≤ (2420256569 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12425 161 ≤ (1614877277 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (97034089 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12425 161 ≤ (978820737 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12425 161 ≤ (696412273 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12425 161 ≤ (50890367 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (508897759 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (508897759 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (409575667 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1525419871 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3698931 / 1000000000) : ℝ) ≤ √(17 / (100 * 12425) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12425) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (563969059 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1619038069 / 40000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12425) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12425) ≤ (56910003 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12425) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12425 * (161 : ℝ) ^ 2 + 26 / (10 * 12425) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12425) : ℝ)) (tA 12425 * 161 ^ 2 + 26 / (10 * 12425)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3698931 / 1000000000))) * ((508897759 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3698931 / 1000000000)) ^ 3) * ((409575667 / 250000000000000000000000))) + ((1525419871 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3698931 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12425) : ℝ)) d.D d.V d.P (√(tA 12425) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3698931 / 1000000000)) ^ 2 * (((563969059 / 250000000000000)) * ((1619038069 / 40000000000000000)))) + ((1525419871 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12425) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3698931 / 1000000000)) * ((508897759 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12425) : ℝ)) (tA 12425 * 161 ^ 2 + 26 / (10 * 12425)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((508897759 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3698931 / 1000000000)) ^ 2) * ((409575667 / 250000000000000000000000)) + ((1525419871 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12425) : ℝ)) (√(26 / (10 * 12425) : ℝ)) d.D d.V d.P (√(tA 12425) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3698931 / 1000000000)) * (((563969059 / 250000000000000)) * ((1619038069 / 40000000000000000))) + ((1525419871 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12425) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((508897759 / 100000000000000000000) : ℝ) + ((1525419871 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12425

namespace BstLean.Part266.Row12425
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12425 161 ∧
    0 ≤ (tableEnvelope C).f1 12425 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12425 161 ∧
    0 ≤ (tableEnvelope C).w1 12425 161 ∧ 0 ≤ (tableEnvelope C).w2 12425 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12425 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12425 161 ∧ 0 ≤ d.f1 12425 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12425 161 ∧ 0 ≤ d.w1 12425 161 ∧ 0 ≤ d.w2 12425 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12425 ≤ 2 * (228 / 100 : ℝ) / 12425 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12425 ≤ 2 * (370 / 100 : ℝ) / 12425 := by
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
    (completeRAData (tableEnvelope C) 12425 161).locationBound 12425 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12425 161).energyBound 12425 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12425 161) (d.f1 12425 161) d.f2 ≤
      32 * (((2420256569 / 500000000000000000) : ℝ) + (1614877277 / 1000000000000000000) + (97034089 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12425 161) (d.w1 12425 161)
      (d.w2 12425 161) ≤
      32 * (((978820737 / 50000000000000000000) : ℝ) + (696412273 / 50000000000000000000) + (50890367 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12425 161) (d.f1 12425 161) d.f2 ≤
      ((2420256569 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2420256569 / 500000000000000000)) * ((1614877277 / 1000000000000000000)) * (126 / 100) +
      2 * (((1614877277 / 1000000000000000000)) ^ 2 + 2 * ((2420256569 / 500000000000000000)) * ((97034089 / 250000000000000000))) +
      6 * ((1614877277 / 1000000000000000000)) * ((97034089 / 250000000000000000)) * (126 / 100) + 8 * ((97034089 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12425 161) (d.f1 12425 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12425 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12425 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12425 161) (d.f1 12425 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12425 161) (d.w1 12425 161) (d.w2 12425 161)
  have hwexpr0 : 0 ≤ d.w0 12425 161 + d.w1 12425 161 * √(π / 2) +
      2 * d.w2 12425 161 + energyR16 12425 *
      radiusPolynomialRoot16 (d.w0 12425 161) (d.w1 12425 161) (d.w2 12425 161) := by
    positivity
  constructor
  · change (12425 : ℝ) ^ 8 * (mA 12425 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12425 161) (d.f1 12425 161) d.f2 + locationR16 12425 *
        radiusPolynomialRoot16 (d.f0 12425 161) (d.f1 12425 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12425 : ℝ) ^ 8 * (mA 12425 : ℝ) ^ 8 *
        ((((2420256569 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2420256569 / 500000000000000000)) * ((1614877277 / 1000000000000000000)) * (126 / 100) +
          2 * (((1614877277 / 1000000000000000000)) ^ 2 + 2 * ((2420256569 / 500000000000000000)) * ((97034089 / 250000000000000000))) +
          6 * ((1614877277 / 1000000000000000000)) * ((97034089 / 250000000000000000)) * (126 / 100) + 8 * ((97034089 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12425) *
          (32 * (((2420256569 / 500000000000000000) : ℝ) + (1614877277 / 1000000000000000000) + (97034089 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12425 : ℝ) ^ 16 *
      (d.w0 12425 161 + d.w1 12425 161 * √(π / 2) + 2 * d.w2 12425 161 +
        energyR16 12425 * radiusPolynomialRoot16 (d.w0 12425 161) (d.w1 12425 161)
          (d.w2 12425 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12425 : ℝ) ^ 16 *
        (((978820737 / 50000000000000000000) : ℝ) + ((696412273 / 50000000000000000000)) * (126 / 100) + 2 * ((50890367 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12425) *
          (32 * (((978820737 / 50000000000000000000) : ℝ) + (696412273 / 50000000000000000000) + (50890367 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12425

/-! A coarse bound on the actual paper statistics constant at dimension 12426. -/
namespace BstLean.Part266.Row12426
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12424 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12424 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12424 128 ≤ (12678 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12678 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12426) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12426 : ℕ))
    (by norm_num : (12426 : ℕ) ≤ 16384)
  have ht : paperTail256 12426 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12426 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12426 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12426 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12426 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12426 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12424 128 * √(2 / (12426 : ℝ)) *
      (√(12426 : ℝ) + paperT0 12426 + paperTail256 12426) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12426 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12426 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12426 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12424 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12424 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12426 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12426

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12426
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12426 (61 / 100) 161 (17 / (100 * 12426)) (26 / (10 * 12426)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12426 (61 / 100) 161 (17 / (100 * 12426)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (508774899 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (409443833 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6097713277 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12426 / 12426 * (61 / 100)) ^ 4 * inverseRadius8 (12426 - 1) /
            envelopeGap 12426 (61 / 100) 161 (17 / (100 * 12426)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12426

namespace BstLean.Part266.Row12426
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12426 161 ≤ (4839539867 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12426 161 ≤ (322910503 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (194029141 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12426 161 ≤ (1957168979 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12426 161 ≤ (278497669 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12426 161 ≤ (254390403 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (508774899 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (508774899 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (409443833 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6097713277 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1849391 / 500000000) : ℝ) ≤ √(17 / (100 * 12426) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12426) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2255603909 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (10117359253 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12426) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12426) ≤ (56905423 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12426) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12426 * (161 : ℝ) ^ 2 + 26 / (10 * 12426) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12426) : ℝ)) (tA 12426 * 161 ^ 2 + 26 / (10 * 12426)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1849391 / 500000000))) * ((508774899 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1849391 / 500000000)) ^ 3) * ((409443833 / 250000000000000000000000))) + ((6097713277 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1849391 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12426) : ℝ)) d.D d.V d.P (√(tA 12426) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1849391 / 500000000)) ^ 2 * (((2255603909 / 1000000000000000)) * ((10117359253 / 250000000000000000)))) + ((6097713277 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12426) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1849391 / 500000000)) * ((508774899 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12426) : ℝ)) (tA 12426 * 161 ^ 2 + 26 / (10 * 12426)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((508774899 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1849391 / 500000000)) ^ 2) * ((409443833 / 250000000000000000000000)) + ((6097713277 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12426) : ℝ)) (√(26 / (10 * 12426) : ℝ)) d.D d.V d.P (√(tA 12426) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1849391 / 500000000)) * (((2255603909 / 1000000000000000)) * ((10117359253 / 250000000000000000))) + ((6097713277 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12426) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((508774899 / 100000000000000000000) : ℝ) + ((6097713277 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12426

namespace BstLean.Part266.Row12426
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12426 161 ∧
    0 ≤ (tableEnvelope C).f1 12426 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12426 161 ∧
    0 ≤ (tableEnvelope C).w1 12426 161 ∧ 0 ≤ (tableEnvelope C).w2 12426 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12426 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12426 161 ∧ 0 ≤ d.f1 12426 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12426 161 ∧ 0 ≤ d.w1 12426 161 ∧ 0 ≤ d.w2 12426 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12426 ≤ 2 * (228 / 100 : ℝ) / 12426 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12426 ≤ 2 * (370 / 100 : ℝ) / 12426 := by
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
    (completeRAData (tableEnvelope C) 12426 161).locationBound 12426 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12426 161).energyBound 12426 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12426 161) (d.f1 12426 161) d.f2 ≤
      32 * (((4839539867 / 1000000000000000000) : ℝ) + (322910503 / 200000000000000000) + (194029141 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12426 161) (d.w1 12426 161)
      (d.w2 12426 161) ≤
      32 * (((1957168979 / 100000000000000000000) : ℝ) + (278497669 / 20000000000000000000) + (254390403 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12426 161) (d.f1 12426 161) d.f2 ≤
      ((4839539867 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4839539867 / 1000000000000000000)) * ((322910503 / 200000000000000000)) * (126 / 100) +
      2 * (((322910503 / 200000000000000000)) ^ 2 + 2 * ((4839539867 / 1000000000000000000)) * ((194029141 / 500000000000000000))) +
      6 * ((322910503 / 200000000000000000)) * ((194029141 / 500000000000000000)) * (126 / 100) + 8 * ((194029141 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12426 161) (d.f1 12426 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12426 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12426 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12426 161) (d.f1 12426 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12426 161) (d.w1 12426 161) (d.w2 12426 161)
  have hwexpr0 : 0 ≤ d.w0 12426 161 + d.w1 12426 161 * √(π / 2) +
      2 * d.w2 12426 161 + energyR16 12426 *
      radiusPolynomialRoot16 (d.w0 12426 161) (d.w1 12426 161) (d.w2 12426 161) := by
    positivity
  constructor
  · change (12426 : ℝ) ^ 8 * (mA 12426 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12426 161) (d.f1 12426 161) d.f2 + locationR16 12426 *
        radiusPolynomialRoot16 (d.f0 12426 161) (d.f1 12426 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12426 : ℝ) ^ 8 * (mA 12426 : ℝ) ^ 8 *
        ((((4839539867 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4839539867 / 1000000000000000000)) * ((322910503 / 200000000000000000)) * (126 / 100) +
          2 * (((322910503 / 200000000000000000)) ^ 2 + 2 * ((4839539867 / 1000000000000000000)) * ((194029141 / 500000000000000000))) +
          6 * ((322910503 / 200000000000000000)) * ((194029141 / 500000000000000000)) * (126 / 100) + 8 * ((194029141 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12426) *
          (32 * (((4839539867 / 1000000000000000000) : ℝ) + (322910503 / 200000000000000000) + (194029141 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12426 : ℝ) ^ 16 *
      (d.w0 12426 161 + d.w1 12426 161 * √(π / 2) + 2 * d.w2 12426 161 +
        energyR16 12426 * radiusPolynomialRoot16 (d.w0 12426 161) (d.w1 12426 161)
          (d.w2 12426 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12426 : ℝ) ^ 16 *
        (((1957168979 / 100000000000000000000) : ℝ) + ((278497669 / 20000000000000000000)) * (126 / 100) + 2 * ((254390403 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12426) *
          (32 * (((1957168979 / 100000000000000000000) : ℝ) + (278497669 / 20000000000000000000) + (254390403 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12426

/-! A coarse bound on the actual paper statistics constant at dimension 12427. -/
namespace BstLean.Part266.Row12427
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12425 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12425 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12425 128 ≤ (12679 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12679 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12427) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12427 : ℕ))
    (by norm_num : (12427 : ℕ) ≤ 16384)
  have ht : paperTail256 12427 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12427 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12427 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12427 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12427 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12427 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12425 128 * √(2 / (12427 : ℝ)) *
      (√(12427 : ℝ) + paperT0 12427 + paperTail256 12427) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12427 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12427 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12427 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12425 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12425 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12427 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12427

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12427
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12427 (61 / 100) 161 (17 / (100 * 12427)) (26 / (10 * 12427)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12427 (61 / 100) 161 (17 / (100 * 12427)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (508652079 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1637248207 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6093749973 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12427 / 12427 * (61 / 100)) ^ 4 * inverseRadius8 (12427 - 1) /
            envelopeGap 12427 (61 / 100) 161 (17 / (100 * 12427)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12427

namespace BstLean.Part266.Row12427
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12427 161 ≤ (2419283467 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12427 161 ≤ (80711393 / 50000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (387980233 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12427 161 ≤ (1956696649 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12427 161 ≤ (69607613 / 5000000000000000000)
  w2 : (tableEnvelope C).w2 12427 161 ≤ (254328991 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (508652079 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (508652079 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1637248207 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6093749973 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3698633 / 1000000000) : ℝ) ≤ √(17 / (100 * 12427) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12427) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2255331637 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40462923857 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12427) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12427) ≤ (113801687 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12427) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12427 * (161 : ℝ) ^ 2 + 26 / (10 * 12427) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12427) : ℝ)) (tA 12427 * 161 ^ 2 + 26 / (10 * 12427)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3698633 / 1000000000))) * ((508652079 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3698633 / 1000000000)) ^ 3) * ((1637248207 / 1000000000000000000000000))) + ((6093749973 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3698633 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12427) : ℝ)) d.D d.V d.P (√(tA 12427) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3698633 / 1000000000)) ^ 2 * (((2255331637 / 1000000000000000)) * ((40462923857 / 1000000000000000000)))) + ((6093749973 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12427) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3698633 / 1000000000)) * ((508652079 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12427) : ℝ)) (tA 12427 * 161 ^ 2 + 26 / (10 * 12427)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((508652079 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3698633 / 1000000000)) ^ 2) * ((1637248207 / 1000000000000000000000000)) + ((6093749973 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12427) : ℝ)) (√(26 / (10 * 12427) : ℝ)) d.D d.V d.P (√(tA 12427) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3698633 / 1000000000)) * (((2255331637 / 1000000000000000)) * ((40462923857 / 1000000000000000000))) + ((6093749973 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12427) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((508652079 / 100000000000000000000) : ℝ) + ((6093749973 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12427

namespace BstLean.Part266.Row12427
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12427 161 ∧
    0 ≤ (tableEnvelope C).f1 12427 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12427 161 ∧
    0 ≤ (tableEnvelope C).w1 12427 161 ∧ 0 ≤ (tableEnvelope C).w2 12427 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12427 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12427 161 ∧ 0 ≤ d.f1 12427 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12427 161 ∧ 0 ≤ d.w1 12427 161 ∧ 0 ≤ d.w2 12427 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12427 ≤ 2 * (228 / 100 : ℝ) / 12427 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12427 ≤ 2 * (370 / 100 : ℝ) / 12427 := by
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
    (completeRAData (tableEnvelope C) 12427 161).locationBound 12427 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12427 161).energyBound 12427 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12427 161) (d.f1 12427 161) d.f2 ≤
      32 * (((2419283467 / 500000000000000000) : ℝ) + (80711393 / 50000000000000000) + (387980233 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12427 161) (d.w1 12427 161)
      (d.w2 12427 161) ≤
      32 * (((1956696649 / 100000000000000000000) : ℝ) + (69607613 / 5000000000000000000) + (254328991 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12427 161) (d.f1 12427 161) d.f2 ≤
      ((2419283467 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2419283467 / 500000000000000000)) * ((80711393 / 50000000000000000)) * (126 / 100) +
      2 * (((80711393 / 50000000000000000)) ^ 2 + 2 * ((2419283467 / 500000000000000000)) * ((387980233 / 1000000000000000000))) +
      6 * ((80711393 / 50000000000000000)) * ((387980233 / 1000000000000000000)) * (126 / 100) + 8 * ((387980233 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12427 161) (d.f1 12427 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12427 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12427 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12427 161) (d.f1 12427 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12427 161) (d.w1 12427 161) (d.w2 12427 161)
  have hwexpr0 : 0 ≤ d.w0 12427 161 + d.w1 12427 161 * √(π / 2) +
      2 * d.w2 12427 161 + energyR16 12427 *
      radiusPolynomialRoot16 (d.w0 12427 161) (d.w1 12427 161) (d.w2 12427 161) := by
    positivity
  constructor
  · change (12427 : ℝ) ^ 8 * (mA 12427 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12427 161) (d.f1 12427 161) d.f2 + locationR16 12427 *
        radiusPolynomialRoot16 (d.f0 12427 161) (d.f1 12427 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12427 : ℝ) ^ 8 * (mA 12427 : ℝ) ^ 8 *
        ((((2419283467 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2419283467 / 500000000000000000)) * ((80711393 / 50000000000000000)) * (126 / 100) +
          2 * (((80711393 / 50000000000000000)) ^ 2 + 2 * ((2419283467 / 500000000000000000)) * ((387980233 / 1000000000000000000))) +
          6 * ((80711393 / 50000000000000000)) * ((387980233 / 1000000000000000000)) * (126 / 100) + 8 * ((387980233 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12427) *
          (32 * (((2419283467 / 500000000000000000) : ℝ) + (80711393 / 50000000000000000) + (387980233 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12427 : ℝ) ^ 16 *
      (d.w0 12427 161 + d.w1 12427 161 * √(π / 2) + 2 * d.w2 12427 161 +
        energyR16 12427 * radiusPolynomialRoot16 (d.w0 12427 161) (d.w1 12427 161)
          (d.w2 12427 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12427 : ℝ) ^ 16 *
        (((1956696649 / 100000000000000000000) : ℝ) + ((69607613 / 5000000000000000000)) * (126 / 100) + 2 * ((254328991 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12427) *
          (32 * (((1956696649 / 100000000000000000000) : ℝ) + (69607613 / 5000000000000000000) + (254328991 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12427

/-! A coarse bound on the actual paper statistics constant at dimension 12428. -/
namespace BstLean.Part266.Row12428
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12426 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12426 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12426 128 ≤ (12680 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12680 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12428) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12428 : ℕ))
    (by norm_num : (12428 : ℕ) ≤ 16384)
  have ht : paperTail256 12428 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12428 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12428 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12428 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12428 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12428 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12426 128 * √(2 / (12428 : ℝ)) *
      (√(12428 : ℝ) + paperT0 12428 + paperTail256 12428) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12428 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12428 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12428 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12426 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12426 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12428 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12428

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12428
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12428 (61 / 100) 161 (17 / (100 * 12428)) (26 / (10 * 12428)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12428 (61 / 100) 161 (17 / (100 * 12428)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (508529299 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (327344259 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6089789571 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12428 / 12428 * (61 / 100)) ^ 4 * inverseRadius8 (12428 - 1) /
            envelopeGap 12428 (61 / 100) 161 (17 / (100 * 12428)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12428

namespace BstLean.Part266.Row12428
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12428 161 ≤ (2418797173 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12428 161 ≤ (1613903313 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (1515243 / 3906250000000000)
  w0 : (tableEnvelope C).w0 12428 161 ≤ (978112243 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12428 161 ≤ (139181629 / 10000000000000000000)
  w2 : (tableEnvelope C).w2 12428 161 ≤ (508535199 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (508529299 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (508529299 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (327344259 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6089789571 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((924621 / 250000000) : ℝ) ≤ √(17 / (100 * 12428) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12428) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2255059421 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (20228206143 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12428) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12428) ≤ (11379253 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12428) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12428 * (161 : ℝ) ^ 2 + 26 / (10 * 12428) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12428) : ℝ)) (tA 12428 * 161 ^ 2 + 26 / (10 * 12428)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((924621 / 250000000))) * ((508529299 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((924621 / 250000000)) ^ 3) * ((327344259 / 200000000000000000000000))) + ((6089789571 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((924621 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12428) : ℝ)) d.D d.V d.P (√(tA 12428) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((924621 / 250000000)) ^ 2 * (((2255059421 / 1000000000000000)) * ((20228206143 / 500000000000000000)))) + ((6089789571 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12428) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((924621 / 250000000)) * ((508529299 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12428) : ℝ)) (tA 12428 * 161 ^ 2 + 26 / (10 * 12428)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((508529299 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((924621 / 250000000)) ^ 2) * ((327344259 / 200000000000000000000000)) + ((6089789571 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12428) : ℝ)) (√(26 / (10 * 12428) : ℝ)) d.D d.V d.P (√(tA 12428) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((924621 / 250000000)) * (((2255059421 / 1000000000000000)) * ((20228206143 / 500000000000000000))) + ((6089789571 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12428) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((508529299 / 100000000000000000000) : ℝ) + ((6089789571 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12428

namespace BstLean.Part266.Row12428
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12428 161 ∧
    0 ≤ (tableEnvelope C).f1 12428 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12428 161 ∧
    0 ≤ (tableEnvelope C).w1 12428 161 ∧ 0 ≤ (tableEnvelope C).w2 12428 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12428 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12428 161 ∧ 0 ≤ d.f1 12428 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12428 161 ∧ 0 ≤ d.w1 12428 161 ∧ 0 ≤ d.w2 12428 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12428 ≤ 2 * (228 / 100 : ℝ) / 12428 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12428 ≤ 2 * (370 / 100 : ℝ) / 12428 := by
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
    (completeRAData (tableEnvelope C) 12428 161).locationBound 12428 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12428 161).energyBound 12428 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12428 161) (d.f1 12428 161) d.f2 ≤
      32 * (((2418797173 / 500000000000000000) : ℝ) + (1613903313 / 1000000000000000000) + (1515243 / 3906250000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12428 161) (d.w1 12428 161)
      (d.w2 12428 161) ≤
      32 * (((978112243 / 50000000000000000000) : ℝ) + (139181629 / 10000000000000000000) + (508535199 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12428 161) (d.f1 12428 161) d.f2 ≤
      ((2418797173 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2418797173 / 500000000000000000)) * ((1613903313 / 1000000000000000000)) * (126 / 100) +
      2 * (((1613903313 / 1000000000000000000)) ^ 2 + 2 * ((2418797173 / 500000000000000000)) * ((1515243 / 3906250000000000))) +
      6 * ((1613903313 / 1000000000000000000)) * ((1515243 / 3906250000000000)) * (126 / 100) + 8 * ((1515243 / 3906250000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12428 161) (d.f1 12428 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12428 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12428 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12428 161) (d.f1 12428 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12428 161) (d.w1 12428 161) (d.w2 12428 161)
  have hwexpr0 : 0 ≤ d.w0 12428 161 + d.w1 12428 161 * √(π / 2) +
      2 * d.w2 12428 161 + energyR16 12428 *
      radiusPolynomialRoot16 (d.w0 12428 161) (d.w1 12428 161) (d.w2 12428 161) := by
    positivity
  constructor
  · change (12428 : ℝ) ^ 8 * (mA 12428 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12428 161) (d.f1 12428 161) d.f2 + locationR16 12428 *
        radiusPolynomialRoot16 (d.f0 12428 161) (d.f1 12428 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12428 : ℝ) ^ 8 * (mA 12428 : ℝ) ^ 8 *
        ((((2418797173 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2418797173 / 500000000000000000)) * ((1613903313 / 1000000000000000000)) * (126 / 100) +
          2 * (((1613903313 / 1000000000000000000)) ^ 2 + 2 * ((2418797173 / 500000000000000000)) * ((1515243 / 3906250000000000))) +
          6 * ((1613903313 / 1000000000000000000)) * ((1515243 / 3906250000000000)) * (126 / 100) + 8 * ((1515243 / 3906250000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12428) *
          (32 * (((2418797173 / 500000000000000000) : ℝ) + (1613903313 / 1000000000000000000) + (1515243 / 3906250000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12428 : ℝ) ^ 16 *
      (d.w0 12428 161 + d.w1 12428 161 * √(π / 2) + 2 * d.w2 12428 161 +
        energyR16 12428 * radiusPolynomialRoot16 (d.w0 12428 161) (d.w1 12428 161)
          (d.w2 12428 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12428 : ℝ) ^ 16 *
        (((978112243 / 50000000000000000000) : ℝ) + ((139181629 / 10000000000000000000)) * (126 / 100) + 2 * ((508535199 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12428) *
          (32 * (((978112243 / 50000000000000000000) : ℝ) + (139181629 / 10000000000000000000) + (508535199 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12428

/-! A coarse bound on the actual paper statistics constant at dimension 12429. -/
namespace BstLean.Part266.Row12429
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12427 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12427 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12427 128 ≤ (12681 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12681 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12429) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12429 : ℕ))
    (by norm_num : (12429 : ℕ) ≤ 16384)
  have ht : paperTail256 12429 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12429 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12429 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12429 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12429 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12429 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12427 128 * √(2 / (12429 : ℝ)) *
      (√(12429 : ℝ) + paperT0 12429 + paperTail256 12429) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12429 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12429 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12429 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12427 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12427 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12429 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12429

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12429
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12429 (61 / 100) 161 (17 / (100 * 12429)) (26 / (10 * 12429)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12429 (61 / 100) 161 (17 / (100 * 12429)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (254203279 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (327238919 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6085832067 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12429 / 12429 * (61 / 100)) ^ 4 * inverseRadius8 (12429 - 1) /
            envelopeGap 12429 (61 / 100) 161 (17 / (100 * 12429)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12429

namespace BstLean.Part266.Row12429
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12429 161 ≤ (1209154581 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12429 161 ≤ (806789 / 500000000000000)
  f2 : (tableEnvelope C).f2 ≤ (387824101 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12429 161 ≤ (977875853 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12429 161 ≤ (695740029 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12429 161 ≤ (254206227 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (254203279 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (254203279 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (327238919 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6085832067 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((115573 / 31250000) : ℝ) ≤ √(17 / (100 * 12429) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12429) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2254787259 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40449902287 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12429) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12429) ≤ (910267 / 8000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12429) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12429 * (161 : ℝ) ^ 2 + 26 / (10 * 12429) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12429) : ℝ)) (tA 12429 * 161 ^ 2 + 26 / (10 * 12429)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((115573 / 31250000))) * ((254203279 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((115573 / 31250000)) ^ 3) * ((327238919 / 200000000000000000000000))) + ((6085832067 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((115573 / 31250000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12429) : ℝ)) d.D d.V d.P (√(tA 12429) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((115573 / 31250000)) ^ 2 * (((2254787259 / 1000000000000000)) * ((40449902287 / 1000000000000000000)))) + ((6085832067 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12429) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((115573 / 31250000)) * ((254203279 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12429) : ℝ)) (tA 12429 * 161 ^ 2 + 26 / (10 * 12429)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((254203279 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((115573 / 31250000)) ^ 2) * ((327238919 / 200000000000000000000000)) + ((6085832067 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12429) : ℝ)) (√(26 / (10 * 12429) : ℝ)) d.D d.V d.P (√(tA 12429) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((115573 / 31250000)) * (((2254787259 / 1000000000000000)) * ((40449902287 / 1000000000000000000))) + ((6085832067 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12429) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((254203279 / 50000000000000000000) : ℝ) + ((6085832067 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12429

namespace BstLean.Part266.Row12429
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12429 161 ∧
    0 ≤ (tableEnvelope C).f1 12429 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12429 161 ∧
    0 ≤ (tableEnvelope C).w1 12429 161 ∧ 0 ≤ (tableEnvelope C).w2 12429 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12429 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12429 161 ∧ 0 ≤ d.f1 12429 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12429 161 ∧ 0 ≤ d.w1 12429 161 ∧ 0 ≤ d.w2 12429 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12429 ≤ 2 * (228 / 100 : ℝ) / 12429 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12429 ≤ 2 * (370 / 100 : ℝ) / 12429 := by
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
    (completeRAData (tableEnvelope C) 12429 161).locationBound 12429 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12429 161).energyBound 12429 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12429 161) (d.f1 12429 161) d.f2 ≤
      32 * (((1209154581 / 250000000000000000) : ℝ) + (806789 / 500000000000000) + (387824101 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12429 161) (d.w1 12429 161)
      (d.w2 12429 161) ≤
      32 * (((977875853 / 50000000000000000000) : ℝ) + (695740029 / 50000000000000000000) + (254206227 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12429 161) (d.f1 12429 161) d.f2 ≤
      ((1209154581 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1209154581 / 250000000000000000)) * ((806789 / 500000000000000)) * (126 / 100) +
      2 * (((806789 / 500000000000000)) ^ 2 + 2 * ((1209154581 / 250000000000000000)) * ((387824101 / 1000000000000000000))) +
      6 * ((806789 / 500000000000000)) * ((387824101 / 1000000000000000000)) * (126 / 100) + 8 * ((387824101 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12429 161) (d.f1 12429 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12429 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12429 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12429 161) (d.f1 12429 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12429 161) (d.w1 12429 161) (d.w2 12429 161)
  have hwexpr0 : 0 ≤ d.w0 12429 161 + d.w1 12429 161 * √(π / 2) +
      2 * d.w2 12429 161 + energyR16 12429 *
      radiusPolynomialRoot16 (d.w0 12429 161) (d.w1 12429 161) (d.w2 12429 161) := by
    positivity
  constructor
  · change (12429 : ℝ) ^ 8 * (mA 12429 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12429 161) (d.f1 12429 161) d.f2 + locationR16 12429 *
        radiusPolynomialRoot16 (d.f0 12429 161) (d.f1 12429 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12429 : ℝ) ^ 8 * (mA 12429 : ℝ) ^ 8 *
        ((((1209154581 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1209154581 / 250000000000000000)) * ((806789 / 500000000000000)) * (126 / 100) +
          2 * (((806789 / 500000000000000)) ^ 2 + 2 * ((1209154581 / 250000000000000000)) * ((387824101 / 1000000000000000000))) +
          6 * ((806789 / 500000000000000)) * ((387824101 / 1000000000000000000)) * (126 / 100) + 8 * ((387824101 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12429) *
          (32 * (((1209154581 / 250000000000000000) : ℝ) + (806789 / 500000000000000) + (387824101 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12429 : ℝ) ^ 16 *
      (d.w0 12429 161 + d.w1 12429 161 * √(π / 2) + 2 * d.w2 12429 161 +
        energyR16 12429 * radiusPolynomialRoot16 (d.w0 12429 161) (d.w1 12429 161)
          (d.w2 12429 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12429 : ℝ) ^ 16 *
        (((977875853 / 50000000000000000000) : ℝ) + ((695740029 / 50000000000000000000)) * (126 / 100) + 2 * ((254206227 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12429) *
          (32 * (((977875853 / 50000000000000000000) : ℝ) + (695740029 / 50000000000000000000) + (254206227 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12429

/-! A coarse bound on the actual paper statistics constant at dimension 12430. -/
namespace BstLean.Part266.Row12430
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12428 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12428 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12428 128 ≤ (12682 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12682 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12430) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12430 : ℕ))
    (by norm_num : (12430 : ℕ) ≤ 16384)
  have ht : paperTail256 12430 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12430 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12430 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12430 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12430 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12430 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12428 128 * √(2 / (12430 : ℝ)) *
      (√(12430 : ℝ) + paperT0 12430 + paperTail256 12430) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12430 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12430 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12430 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12428 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12428 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12430 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12430

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12430
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12430 (61 / 100) 161 (17 / (100 * 12430)) (26 / (10 * 12430)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12430 (61 / 100) 161 (17 / (100 * 12430)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (31767741 / 6250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (817834053 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3040938729 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12430 / 12430 * (61 / 100)) ^ 4 * inverseRadius8 (12430 - 1) /
            envelopeGap 12430 (61 / 100) 161 (17 / (100 * 12430)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12430

namespace BstLean.Part266.Row12430
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12430 161 ≤ (4835646417 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12430 161 ≤ (322650733 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (387746123 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12430 161 ≤ (977639937 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12430 161 ≤ (347786079 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12430 161 ≤ (127072437 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (31767741 / 6250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (31767741 / 6250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (817834053 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3040938729 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3698187 / 1000000000) : ℝ) ≤ √(17 / (100 * 12430) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12430) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (45090303 / 20000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40443393849 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12430) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12430) ≤ (113774221 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12430) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12430 * (161 : ℝ) ^ 2 + 26 / (10 * 12430) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12430) : ℝ)) (tA 12430 * 161 ^ 2 + 26 / (10 * 12430)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3698187 / 1000000000))) * ((31767741 / 6250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3698187 / 1000000000)) ^ 3) * ((817834053 / 500000000000000000000000))) + ((3040938729 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3698187 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12430) : ℝ)) d.D d.V d.P (√(tA 12430) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3698187 / 1000000000)) ^ 2 * (((45090303 / 20000000000000)) * ((40443393849 / 1000000000000000000)))) + ((3040938729 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12430) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3698187 / 1000000000)) * ((31767741 / 6250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12430) : ℝ)) (tA 12430 * 161 ^ 2 + 26 / (10 * 12430)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((31767741 / 6250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3698187 / 1000000000)) ^ 2) * ((817834053 / 500000000000000000000000)) + ((3040938729 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12430) : ℝ)) (√(26 / (10 * 12430) : ℝ)) d.D d.V d.P (√(tA 12430) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3698187 / 1000000000)) * (((45090303 / 20000000000000)) * ((40443393849 / 1000000000000000000))) + ((3040938729 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12430) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((31767741 / 6250000000000000000) : ℝ) + ((3040938729 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12430

namespace BstLean.Part266.Row12430
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12430 161 ∧
    0 ≤ (tableEnvelope C).f1 12430 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12430 161 ∧
    0 ≤ (tableEnvelope C).w1 12430 161 ∧ 0 ≤ (tableEnvelope C).w2 12430 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12430 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12430 161 ∧ 0 ≤ d.f1 12430 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12430 161 ∧ 0 ≤ d.w1 12430 161 ∧ 0 ≤ d.w2 12430 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12430 ≤ 2 * (228 / 100 : ℝ) / 12430 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12430 ≤ 2 * (370 / 100 : ℝ) / 12430 := by
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
    (completeRAData (tableEnvelope C) 12430 161).locationBound 12430 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12430 161).energyBound 12430 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12430 161) (d.f1 12430 161) d.f2 ≤
      32 * (((4835646417 / 1000000000000000000) : ℝ) + (322650733 / 200000000000000000) + (387746123 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12430 161) (d.w1 12430 161)
      (d.w2 12430 161) ≤
      32 * (((977639937 / 50000000000000000000) : ℝ) + (347786079 / 25000000000000000000) + (127072437 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12430 161) (d.f1 12430 161) d.f2 ≤
      ((4835646417 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4835646417 / 1000000000000000000)) * ((322650733 / 200000000000000000)) * (126 / 100) +
      2 * (((322650733 / 200000000000000000)) ^ 2 + 2 * ((4835646417 / 1000000000000000000)) * ((387746123 / 1000000000000000000))) +
      6 * ((322650733 / 200000000000000000)) * ((387746123 / 1000000000000000000)) * (126 / 100) + 8 * ((387746123 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12430 161) (d.f1 12430 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12430 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12430 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12430 161) (d.f1 12430 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12430 161) (d.w1 12430 161) (d.w2 12430 161)
  have hwexpr0 : 0 ≤ d.w0 12430 161 + d.w1 12430 161 * √(π / 2) +
      2 * d.w2 12430 161 + energyR16 12430 *
      radiusPolynomialRoot16 (d.w0 12430 161) (d.w1 12430 161) (d.w2 12430 161) := by
    positivity
  constructor
  · change (12430 : ℝ) ^ 8 * (mA 12430 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12430 161) (d.f1 12430 161) d.f2 + locationR16 12430 *
        radiusPolynomialRoot16 (d.f0 12430 161) (d.f1 12430 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12430 : ℝ) ^ 8 * (mA 12430 : ℝ) ^ 8 *
        ((((4835646417 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4835646417 / 1000000000000000000)) * ((322650733 / 200000000000000000)) * (126 / 100) +
          2 * (((322650733 / 200000000000000000)) ^ 2 + 2 * ((4835646417 / 1000000000000000000)) * ((387746123 / 1000000000000000000))) +
          6 * ((322650733 / 200000000000000000)) * ((387746123 / 1000000000000000000)) * (126 / 100) + 8 * ((387746123 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12430) *
          (32 * (((4835646417 / 1000000000000000000) : ℝ) + (322650733 / 200000000000000000) + (387746123 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12430 : ℝ) ^ 16 *
      (d.w0 12430 161 + d.w1 12430 161 * √(π / 2) + 2 * d.w2 12430 161 +
        energyR16 12430 * radiusPolynomialRoot16 (d.w0 12430 161) (d.w1 12430 161)
          (d.w2 12430 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12430 : ℝ) ^ 16 *
        (((977639937 / 50000000000000000000) : ℝ) + ((347786079 / 25000000000000000000)) * (126 / 100) + 2 * ((127072437 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12430) *
          (32 * (((977639937 / 50000000000000000000) : ℝ) + (347786079 / 25000000000000000000) + (127072437 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12430

/-! A coarse bound on the actual paper statistics constant at dimension 12431. -/
namespace BstLean.Part266.Row12431
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12429 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12429 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12429 128 ≤ (12683 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12683 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12431) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12431 : ℕ))
    (by norm_num : (12431 : ℕ) ≤ 16384)
  have ht : paperTail256 12431 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12431 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12431 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12431 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12431 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12431 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12429 128 * √(2 / (12431 : ℝ)) *
      (√(12431 : ℝ) + paperT0 12431 + paperTail256 12431) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12431 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12431 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12431 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12429 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12429 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12431 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12431

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12431
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12431 (61 / 100) 161 (17 / (100 * 12431)) (26 / (10 * 12431)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12431 (61 / 100) 161 (17 / (100 * 12431)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (254080597 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1635141829 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (379870359 / 62500000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12431 / 12431 * (61 / 100)) ^ 4 * inverseRadius8 (12431 - 1) /
            envelopeGap 12431 (61 / 100) 161 (17 / (100 * 12431)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12431

namespace BstLean.Part266.Row12431
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12431 161 ≤ (1208668713 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12431 161 ≤ (806464719 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (387668169 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12431 161 ≤ (122175513 / 6250000000000000000)
  w1 : (tableEnvelope C).w1 12431 161 ≤ (139080869 / 10000000000000000000)
  w2 : (tableEnvelope C).w2 12431 161 ≤ (254083541 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (254080597 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (254080597 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1635141829 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (379870359 / 62500000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1849019 / 500000000) : ℝ) ≤ √(17 / (100 * 12431) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12431) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2254243097 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (8087377397 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12431) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12431) ≤ (113765069 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12431) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12431 * (161 : ℝ) ^ 2 + 26 / (10 * 12431) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12431) : ℝ)) (tA 12431 * 161 ^ 2 + 26 / (10 * 12431)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1849019 / 500000000))) * ((254080597 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1849019 / 500000000)) ^ 3) * ((1635141829 / 1000000000000000000000000))) + ((379870359 / 62500000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1849019 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12431) : ℝ)) d.D d.V d.P (√(tA 12431) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1849019 / 500000000)) ^ 2 * (((2254243097 / 1000000000000000)) * ((8087377397 / 200000000000000000)))) + ((379870359 / 62500000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12431) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1849019 / 500000000)) * ((254080597 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12431) : ℝ)) (tA 12431 * 161 ^ 2 + 26 / (10 * 12431)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((254080597 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1849019 / 500000000)) ^ 2) * ((1635141829 / 1000000000000000000000000)) + ((379870359 / 62500000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12431) : ℝ)) (√(26 / (10 * 12431) : ℝ)) d.D d.V d.P (√(tA 12431) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1849019 / 500000000)) * (((2254243097 / 1000000000000000)) * ((8087377397 / 200000000000000000))) + ((379870359 / 62500000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12431) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((254080597 / 50000000000000000000) : ℝ) + ((379870359 / 62500000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12431

namespace BstLean.Part266.Row12431
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12431 161 ∧
    0 ≤ (tableEnvelope C).f1 12431 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12431 161 ∧
    0 ≤ (tableEnvelope C).w1 12431 161 ∧ 0 ≤ (tableEnvelope C).w2 12431 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12431 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12431 161 ∧ 0 ≤ d.f1 12431 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12431 161 ∧ 0 ≤ d.w1 12431 161 ∧ 0 ≤ d.w2 12431 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12431 ≤ 2 * (228 / 100 : ℝ) / 12431 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12431 ≤ 2 * (370 / 100 : ℝ) / 12431 := by
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
    (completeRAData (tableEnvelope C) 12431 161).locationBound 12431 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12431 161).energyBound 12431 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12431 161) (d.f1 12431 161) d.f2 ≤
      32 * (((1208668713 / 250000000000000000) : ℝ) + (806464719 / 500000000000000000) + (387668169 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12431 161) (d.w1 12431 161)
      (d.w2 12431 161) ≤
      32 * (((122175513 / 6250000000000000000) : ℝ) + (139080869 / 10000000000000000000) + (254083541 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12431 161) (d.f1 12431 161) d.f2 ≤
      ((1208668713 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1208668713 / 250000000000000000)) * ((806464719 / 500000000000000000)) * (126 / 100) +
      2 * (((806464719 / 500000000000000000)) ^ 2 + 2 * ((1208668713 / 250000000000000000)) * ((387668169 / 1000000000000000000))) +
      6 * ((806464719 / 500000000000000000)) * ((387668169 / 1000000000000000000)) * (126 / 100) + 8 * ((387668169 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12431 161) (d.f1 12431 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12431 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12431 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12431 161) (d.f1 12431 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12431 161) (d.w1 12431 161) (d.w2 12431 161)
  have hwexpr0 : 0 ≤ d.w0 12431 161 + d.w1 12431 161 * √(π / 2) +
      2 * d.w2 12431 161 + energyR16 12431 *
      radiusPolynomialRoot16 (d.w0 12431 161) (d.w1 12431 161) (d.w2 12431 161) := by
    positivity
  constructor
  · change (12431 : ℝ) ^ 8 * (mA 12431 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12431 161) (d.f1 12431 161) d.f2 + locationR16 12431 *
        radiusPolynomialRoot16 (d.f0 12431 161) (d.f1 12431 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12431 : ℝ) ^ 8 * (mA 12431 : ℝ) ^ 8 *
        ((((1208668713 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1208668713 / 250000000000000000)) * ((806464719 / 500000000000000000)) * (126 / 100) +
          2 * (((806464719 / 500000000000000000)) ^ 2 + 2 * ((1208668713 / 250000000000000000)) * ((387668169 / 1000000000000000000))) +
          6 * ((806464719 / 500000000000000000)) * ((387668169 / 1000000000000000000)) * (126 / 100) + 8 * ((387668169 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12431) *
          (32 * (((1208668713 / 250000000000000000) : ℝ) + (806464719 / 500000000000000000) + (387668169 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12431 : ℝ) ^ 16 *
      (d.w0 12431 161 + d.w1 12431 161 * √(π / 2) + 2 * d.w2 12431 161 +
        energyR16 12431 * radiusPolynomialRoot16 (d.w0 12431 161) (d.w1 12431 161)
          (d.w2 12431 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12431 : ℝ) ^ 16 *
        (((122175513 / 6250000000000000000) : ℝ) + ((139080869 / 10000000000000000000)) * (126 / 100) + 2 * ((254083541 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12431) *
          (32 * (((122175513 / 6250000000000000000) : ℝ) + (139080869 / 10000000000000000000) + (254083541 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12431

/-! A coarse bound on the actual paper statistics constant at dimension 12432. -/
namespace BstLean.Part266.Row12432
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12430 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12430 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12430 128 ≤ (12684 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12684 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12432) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12432 : ℕ))
    (by norm_num : (12432 : ℕ) ≤ 16384)
  have ht : paperTail256 12432 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12432 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12432 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12432 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12432 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12432 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12430 128 * √(2 / (12432 : ℝ)) *
      (√(12432 : ℝ) + paperT0 12432 + paperTail256 12432) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12432 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12432 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12432 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12430 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12430 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12432 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12432

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12432
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12432 (61 / 100) 161 (17 / (100 * 12432)) (26 / (10 * 12432)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12432 (61 / 100) 161 (17 / (100 * 12432)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (127009643 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (408653941 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6073976921 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12432 / 12432 * (61 / 100)) ^ 4 * inverseRadius8 (12432 - 1) /
            envelopeGap 12432 (61 / 100) 161 (17 / (100 * 12432)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12432

namespace BstLean.Part266.Row12432
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12432 161 ≤ (483370363 / 100000000000000000)
  f1 : (tableEnvelope C).f1 12432 161 ≤ (40315133 / 25000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (387590239 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12432 161 ≤ (1954336709 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12432 161 ≤ (69523659 / 5000000000000000000)
  w2 : (tableEnvelope C).w2 12432 161 ≤ (63505557 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (127009643 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (127009643 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (408653941 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6073976921 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3697889 / 1000000000) : ℝ) ≤ √(17 / (100 * 12432) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12432) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2253971101 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (8086076339 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12432) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12432) ≤ (56877959 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12432) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12432 * (161 : ℝ) ^ 2 + 26 / (10 * 12432) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12432) : ℝ)) (tA 12432 * 161 ^ 2 + 26 / (10 * 12432)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3697889 / 1000000000))) * ((127009643 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3697889 / 1000000000)) ^ 3) * ((408653941 / 250000000000000000000000))) + ((6073976921 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3697889 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12432) : ℝ)) d.D d.V d.P (√(tA 12432) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3697889 / 1000000000)) ^ 2 * (((2253971101 / 1000000000000000)) * ((8086076339 / 200000000000000000)))) + ((6073976921 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12432) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3697889 / 1000000000)) * ((127009643 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12432) : ℝ)) (tA 12432 * 161 ^ 2 + 26 / (10 * 12432)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((127009643 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3697889 / 1000000000)) ^ 2) * ((408653941 / 250000000000000000000000)) + ((6073976921 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12432) : ℝ)) (√(26 / (10 * 12432) : ℝ)) d.D d.V d.P (√(tA 12432) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3697889 / 1000000000)) * (((2253971101 / 1000000000000000)) * ((8086076339 / 200000000000000000))) + ((6073976921 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12432) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((127009643 / 25000000000000000000) : ℝ) + ((6073976921 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12432

namespace BstLean.Part266.Row12432
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12432 161 ∧
    0 ≤ (tableEnvelope C).f1 12432 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12432 161 ∧
    0 ≤ (tableEnvelope C).w1 12432 161 ∧ 0 ≤ (tableEnvelope C).w2 12432 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12432 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12432 161 ∧ 0 ≤ d.f1 12432 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12432 161 ∧ 0 ≤ d.w1 12432 161 ∧ 0 ≤ d.w2 12432 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12432 ≤ 2 * (228 / 100 : ℝ) / 12432 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12432 ≤ 2 * (370 / 100 : ℝ) / 12432 := by
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
    (completeRAData (tableEnvelope C) 12432 161).locationBound 12432 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12432 161).energyBound 12432 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12432 161) (d.f1 12432 161) d.f2 ≤
      32 * (((483370363 / 100000000000000000) : ℝ) + (40315133 / 25000000000000000) + (387590239 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12432 161) (d.w1 12432 161)
      (d.w2 12432 161) ≤
      32 * (((1954336709 / 100000000000000000000) : ℝ) + (69523659 / 5000000000000000000) + (63505557 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12432 161) (d.f1 12432 161) d.f2 ≤
      ((483370363 / 100000000000000000) : ℝ) ^ 2 + 2 * ((483370363 / 100000000000000000)) * ((40315133 / 25000000000000000)) * (126 / 100) +
      2 * (((40315133 / 25000000000000000)) ^ 2 + 2 * ((483370363 / 100000000000000000)) * ((387590239 / 1000000000000000000))) +
      6 * ((40315133 / 25000000000000000)) * ((387590239 / 1000000000000000000)) * (126 / 100) + 8 * ((387590239 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12432 161) (d.f1 12432 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12432 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12432 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12432 161) (d.f1 12432 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12432 161) (d.w1 12432 161) (d.w2 12432 161)
  have hwexpr0 : 0 ≤ d.w0 12432 161 + d.w1 12432 161 * √(π / 2) +
      2 * d.w2 12432 161 + energyR16 12432 *
      radiusPolynomialRoot16 (d.w0 12432 161) (d.w1 12432 161) (d.w2 12432 161) := by
    positivity
  constructor
  · change (12432 : ℝ) ^ 8 * (mA 12432 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12432 161) (d.f1 12432 161) d.f2 + locationR16 12432 *
        radiusPolynomialRoot16 (d.f0 12432 161) (d.f1 12432 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12432 : ℝ) ^ 8 * (mA 12432 : ℝ) ^ 8 *
        ((((483370363 / 100000000000000000) : ℝ) ^ 2 + 2 * ((483370363 / 100000000000000000)) * ((40315133 / 25000000000000000)) * (126 / 100) +
          2 * (((40315133 / 25000000000000000)) ^ 2 + 2 * ((483370363 / 100000000000000000)) * ((387590239 / 1000000000000000000))) +
          6 * ((40315133 / 25000000000000000)) * ((387590239 / 1000000000000000000)) * (126 / 100) + 8 * ((387590239 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12432) *
          (32 * (((483370363 / 100000000000000000) : ℝ) + (40315133 / 25000000000000000) + (387590239 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12432 : ℝ) ^ 16 *
      (d.w0 12432 161 + d.w1 12432 161 * √(π / 2) + 2 * d.w2 12432 161 +
        energyR16 12432 * radiusPolynomialRoot16 (d.w0 12432 161) (d.w1 12432 161)
          (d.w2 12432 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12432 : ℝ) ^ 16 *
        (((1954336709 / 100000000000000000000) : ℝ) + ((69523659 / 5000000000000000000)) * (126 / 100) + 2 * ((63505557 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12432) *
          (32 * (((1954336709 / 100000000000000000000) : ℝ) + (69523659 / 5000000000000000000) + (63505557 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12432

/-! A coarse bound on the actual paper statistics constant at dimension 12433. -/
namespace BstLean.Part266.Row12433
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12431 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12431 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12431 128 ≤ (12685 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12685 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12433) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12433 : ℕ))
    (by norm_num : (12433 : ℕ) ≤ 16384)
  have ht : paperTail256 12433 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12433 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12433 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12433 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12433 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12433 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12431 128 * √(2 / (12433 : ℝ)) *
      (√(12433 : ℝ) + paperT0 12433 + paperTail256 12433) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12433 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12433 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12433 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12431 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12431 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12433 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12433

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12433
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12433 (61 / 100) 161 (17 / (100 * 12433)) (26 / (10 * 12433)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12433 (61 / 100) 161 (17 / (100 * 12433)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (507915989 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1634089911 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6070030987 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12433 / 12433 * (61 / 100)) ^ 4 * inverseRadius8 (12433 - 1) /
            envelopeGap 12433 (61 / 100) 161 (17 / (100 * 12433)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12433

namespace BstLean.Part266.Row12433
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12433 161 ≤ (4832728977 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12433 161 ≤ (322456087 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (96878057 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12433 161 ≤ (976932297 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12433 161 ≤ (21720897 / 1562500000000000000)
  w2 : (tableEnvelope C).w2 12433 161 ≤ (507921869 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (507915989 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (507915989 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1634089911 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6070030987 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3697741 / 1000000000) : ℝ) ≤ √(17 / (100 * 12433) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12433) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2253699157 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40423877981 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12433) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12433) ≤ (7109173 / 62500000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12433) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12433 * (161 : ℝ) ^ 2 + 26 / (10 * 12433) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12433) : ℝ)) (tA 12433 * 161 ^ 2 + 26 / (10 * 12433)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3697741 / 1000000000))) * ((507915989 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3697741 / 1000000000)) ^ 3) * ((1634089911 / 1000000000000000000000000))) + ((6070030987 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3697741 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12433) : ℝ)) d.D d.V d.P (√(tA 12433) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3697741 / 1000000000)) ^ 2 * (((2253699157 / 1000000000000000)) * ((40423877981 / 1000000000000000000)))) + ((6070030987 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12433) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3697741 / 1000000000)) * ((507915989 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12433) : ℝ)) (tA 12433 * 161 ^ 2 + 26 / (10 * 12433)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((507915989 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3697741 / 1000000000)) ^ 2) * ((1634089911 / 1000000000000000000000000)) + ((6070030987 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12433) : ℝ)) (√(26 / (10 * 12433) : ℝ)) d.D d.V d.P (√(tA 12433) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3697741 / 1000000000)) * (((2253699157 / 1000000000000000)) * ((40423877981 / 1000000000000000000))) + ((6070030987 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12433) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((507915989 / 100000000000000000000) : ℝ) + ((6070030987 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12433

namespace BstLean.Part266.Row12433
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12433 161 ∧
    0 ≤ (tableEnvelope C).f1 12433 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12433 161 ∧
    0 ≤ (tableEnvelope C).w1 12433 161 ∧ 0 ≤ (tableEnvelope C).w2 12433 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12433 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12433 161 ∧ 0 ≤ d.f1 12433 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12433 161 ∧ 0 ≤ d.w1 12433 161 ∧ 0 ≤ d.w2 12433 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12433 ≤ 2 * (228 / 100 : ℝ) / 12433 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12433 ≤ 2 * (370 / 100 : ℝ) / 12433 := by
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
    (completeRAData (tableEnvelope C) 12433 161).locationBound 12433 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12433 161).energyBound 12433 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12433 161) (d.f1 12433 161) d.f2 ≤
      32 * (((4832728977 / 1000000000000000000) : ℝ) + (322456087 / 200000000000000000) + (96878057 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12433 161) (d.w1 12433 161)
      (d.w2 12433 161) ≤
      32 * (((976932297 / 50000000000000000000) : ℝ) + (21720897 / 1562500000000000000) + (507921869 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12433 161) (d.f1 12433 161) d.f2 ≤
      ((4832728977 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4832728977 / 1000000000000000000)) * ((322456087 / 200000000000000000)) * (126 / 100) +
      2 * (((322456087 / 200000000000000000)) ^ 2 + 2 * ((4832728977 / 1000000000000000000)) * ((96878057 / 250000000000000000))) +
      6 * ((322456087 / 200000000000000000)) * ((96878057 / 250000000000000000)) * (126 / 100) + 8 * ((96878057 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12433 161) (d.f1 12433 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12433 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12433 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12433 161) (d.f1 12433 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12433 161) (d.w1 12433 161) (d.w2 12433 161)
  have hwexpr0 : 0 ≤ d.w0 12433 161 + d.w1 12433 161 * √(π / 2) +
      2 * d.w2 12433 161 + energyR16 12433 *
      radiusPolynomialRoot16 (d.w0 12433 161) (d.w1 12433 161) (d.w2 12433 161) := by
    positivity
  constructor
  · change (12433 : ℝ) ^ 8 * (mA 12433 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12433 161) (d.f1 12433 161) d.f2 + locationR16 12433 *
        radiusPolynomialRoot16 (d.f0 12433 161) (d.f1 12433 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12433 : ℝ) ^ 8 * (mA 12433 : ℝ) ^ 8 *
        ((((4832728977 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4832728977 / 1000000000000000000)) * ((322456087 / 200000000000000000)) * (126 / 100) +
          2 * (((322456087 / 200000000000000000)) ^ 2 + 2 * ((4832728977 / 1000000000000000000)) * ((96878057 / 250000000000000000))) +
          6 * ((322456087 / 200000000000000000)) * ((96878057 / 250000000000000000)) * (126 / 100) + 8 * ((96878057 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12433) *
          (32 * (((4832728977 / 1000000000000000000) : ℝ) + (322456087 / 200000000000000000) + (96878057 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12433 : ℝ) ^ 16 *
      (d.w0 12433 161 + d.w1 12433 161 * √(π / 2) + 2 * d.w2 12433 161 +
        energyR16 12433 * radiusPolynomialRoot16 (d.w0 12433 161) (d.w1 12433 161)
          (d.w2 12433 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12433 : ℝ) ^ 16 *
        (((976932297 / 50000000000000000000) : ℝ) + ((21720897 / 1562500000000000000)) * (126 / 100) + 2 * ((507921869 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12433) *
          (32 * (((976932297 / 50000000000000000000) : ℝ) + (21720897 / 1562500000000000000) + (507921869 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12433

/-! A coarse bound on the actual paper statistics constant at dimension 12434. -/
namespace BstLean.Part266.Row12434
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12432 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12432 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12432 128 ≤ (12686 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12686 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12434) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12434 : ℕ))
    (by norm_num : (12434 : ℕ) ≤ 16384)
  have ht : paperTail256 12434 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12434 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12434 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12434 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12434 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12434 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12432 128 * √(2 / (12434 : ℝ)) *
      (√(12434 : ℝ) + paperT0 12434 + paperTail256 12434) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12434 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12434 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12434 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12432 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12432 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12434 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12434

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12434
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12434 (61 / 100) 161 (17 / (100 * 12434)) (26 / (10 * 12434)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12434 (61 / 100) 161 (17 / (100 * 12434)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (101558689 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1633564269 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (303304397 / 50000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12434 / 12434 * (61 / 100)) ^ 4 * inverseRadius8 (12434 - 1) /
            envelopeGap 12434 (61 / 100) 161 (17 / (100 * 12434)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12434

namespace BstLean.Part266.Row12434
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12434 161 ≤ (4831758437 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12434 161 ≤ (1611956529 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (77486869 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12434 161 ≤ (78135737 / 4000000000000000000)
  w1 : (tableEnvelope C).w1 12434 161 ≤ (694901063 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12434 161 ≤ (253899661 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (101558689 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (101558689 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1633564269 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (303304397 / 50000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((462199 / 125000000) : ℝ) ≤ √(17 / (100 * 12434) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12434) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (563356817 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40417375831 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12434) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12434) ≤ (5686881 / 50000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12434) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12434 * (161 : ℝ) ^ 2 + 26 / (10 * 12434) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12434) : ℝ)) (tA 12434 * 161 ^ 2 + 26 / (10 * 12434)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((462199 / 125000000))) * ((101558689 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((462199 / 125000000)) ^ 3) * ((1633564269 / 1000000000000000000000000))) + ((303304397 / 50000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((462199 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12434) : ℝ)) d.D d.V d.P (√(tA 12434) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((462199 / 125000000)) ^ 2 * (((563356817 / 250000000000000)) * ((40417375831 / 1000000000000000000)))) + ((303304397 / 50000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12434) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((462199 / 125000000)) * ((101558689 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12434) : ℝ)) (tA 12434 * 161 ^ 2 + 26 / (10 * 12434)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((101558689 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((462199 / 125000000)) ^ 2) * ((1633564269 / 1000000000000000000000000)) + ((303304397 / 50000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12434) : ℝ)) (√(26 / (10 * 12434) : ℝ)) d.D d.V d.P (√(tA 12434) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((462199 / 125000000)) * (((563356817 / 250000000000000)) * ((40417375831 / 1000000000000000000))) + ((303304397 / 50000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12434) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((101558689 / 20000000000000000000) : ℝ) + ((303304397 / 50000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12434

namespace BstLean.Part266.Row12434
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12434 161 ∧
    0 ≤ (tableEnvelope C).f1 12434 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12434 161 ∧
    0 ≤ (tableEnvelope C).w1 12434 161 ∧ 0 ≤ (tableEnvelope C).w2 12434 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12434 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12434 161 ∧ 0 ≤ d.f1 12434 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12434 161 ∧ 0 ≤ d.w1 12434 161 ∧ 0 ≤ d.w2 12434 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12434 ≤ 2 * (228 / 100 : ℝ) / 12434 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12434 ≤ 2 * (370 / 100 : ℝ) / 12434 := by
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
    (completeRAData (tableEnvelope C) 12434 161).locationBound 12434 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12434 161).energyBound 12434 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12434 161) (d.f1 12434 161) d.f2 ≤
      32 * (((4831758437 / 1000000000000000000) : ℝ) + (1611956529 / 1000000000000000000) + (77486869 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12434 161) (d.w1 12434 161)
      (d.w2 12434 161) ≤
      32 * (((78135737 / 4000000000000000000) : ℝ) + (694901063 / 50000000000000000000) + (253899661 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12434 161) (d.f1 12434 161) d.f2 ≤
      ((4831758437 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4831758437 / 1000000000000000000)) * ((1611956529 / 1000000000000000000)) * (126 / 100) +
      2 * (((1611956529 / 1000000000000000000)) ^ 2 + 2 * ((4831758437 / 1000000000000000000)) * ((77486869 / 200000000000000000))) +
      6 * ((1611956529 / 1000000000000000000)) * ((77486869 / 200000000000000000)) * (126 / 100) + 8 * ((77486869 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12434 161) (d.f1 12434 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12434 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12434 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12434 161) (d.f1 12434 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12434 161) (d.w1 12434 161) (d.w2 12434 161)
  have hwexpr0 : 0 ≤ d.w0 12434 161 + d.w1 12434 161 * √(π / 2) +
      2 * d.w2 12434 161 + energyR16 12434 *
      radiusPolynomialRoot16 (d.w0 12434 161) (d.w1 12434 161) (d.w2 12434 161) := by
    positivity
  constructor
  · change (12434 : ℝ) ^ 8 * (mA 12434 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12434 161) (d.f1 12434 161) d.f2 + locationR16 12434 *
        radiusPolynomialRoot16 (d.f0 12434 161) (d.f1 12434 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12434 : ℝ) ^ 8 * (mA 12434 : ℝ) ^ 8 *
        ((((4831758437 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4831758437 / 1000000000000000000)) * ((1611956529 / 1000000000000000000)) * (126 / 100) +
          2 * (((1611956529 / 1000000000000000000)) ^ 2 + 2 * ((4831758437 / 1000000000000000000)) * ((77486869 / 200000000000000000))) +
          6 * ((1611956529 / 1000000000000000000)) * ((77486869 / 200000000000000000)) * (126 / 100) + 8 * ((77486869 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12434) *
          (32 * (((4831758437 / 1000000000000000000) : ℝ) + (1611956529 / 1000000000000000000) + (77486869 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12434 : ℝ) ^ 16 *
      (d.w0 12434 161 + d.w1 12434 161 * √(π / 2) + 2 * d.w2 12434 161 +
        energyR16 12434 * radiusPolynomialRoot16 (d.w0 12434 161) (d.w1 12434 161)
          (d.w2 12434 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12434 : ℝ) ^ 16 *
        (((78135737 / 4000000000000000000) : ℝ) + ((694901063 / 50000000000000000000)) * (126 / 100) + 2 * ((253899661 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12434) *
          (32 * (((78135737 / 4000000000000000000) : ℝ) + (694901063 / 50000000000000000000) + (253899661 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12434

/-! A coarse bound on the actual paper statistics constant at dimension 12435. -/
namespace BstLean.Part266.Row12435
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12433 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12433 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12433 128 ≤ (12687 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12687 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12435) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12435 : ℕ))
    (by norm_num : (12435 : ℕ) ≤ 16384)
  have ht : paperTail256 12435 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12435 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12435 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12435 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12435 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12435 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12433 128 * √(2 / (12435 : ℝ)) *
      (√(12435 : ℝ) + paperT0 12435 + paperTail256 12435) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12435 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12435 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12435 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12433 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12433 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12435 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12435

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12435
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12435 (61 / 100) 161 (17 / (100 * 12435)) (26 / (10 * 12435)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12435 (61 / 100) 161 (17 / (100 * 12435)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (507670941 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (816519419 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6062147777 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12435 / 12435 * (61 / 100)) ^ 4 * inverseRadius8 (12435 - 1) /
            envelopeGap 12435 (61 / 100) 161 (17 / (100 * 12435)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12435

namespace BstLean.Part266.Row12435
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12435 161 ≤ (4830788237 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12435 161 ≤ (161163273 / 100000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (387356487 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12435 161 ≤ (1952922423 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12435 161 ≤ (1389466959 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12435 161 ≤ (253838407 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (507670941 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (507670941 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (816519419 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6062147777 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3697443 / 1000000000) : ℝ) ≤ √(17 / (100 * 12435) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12435) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (450631087 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (8082175049 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12435) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12435) ≤ (56864237 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12435) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12435 * (161 : ℝ) ^ 2 + 26 / (10 * 12435) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12435) : ℝ)) (tA 12435 * 161 ^ 2 + 26 / (10 * 12435)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3697443 / 1000000000))) * ((507670941 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3697443 / 1000000000)) ^ 3) * ((816519419 / 500000000000000000000000))) + ((6062147777 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3697443 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12435) : ℝ)) d.D d.V d.P (√(tA 12435) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3697443 / 1000000000)) ^ 2 * (((450631087 / 200000000000000)) * ((8082175049 / 200000000000000000)))) + ((6062147777 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12435) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3697443 / 1000000000)) * ((507670941 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12435) : ℝ)) (tA 12435 * 161 ^ 2 + 26 / (10 * 12435)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((507670941 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3697443 / 1000000000)) ^ 2) * ((816519419 / 500000000000000000000000)) + ((6062147777 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12435) : ℝ)) (√(26 / (10 * 12435) : ℝ)) d.D d.V d.P (√(tA 12435) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3697443 / 1000000000)) * (((450631087 / 200000000000000)) * ((8082175049 / 200000000000000000))) + ((6062147777 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12435) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((507670941 / 100000000000000000000) : ℝ) + ((6062147777 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12435

namespace BstLean.Part266.Row12435
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12435 161 ∧
    0 ≤ (tableEnvelope C).f1 12435 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12435 161 ∧
    0 ≤ (tableEnvelope C).w1 12435 161 ∧ 0 ≤ (tableEnvelope C).w2 12435 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12435 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12435 161 ∧ 0 ≤ d.f1 12435 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12435 161 ∧ 0 ≤ d.w1 12435 161 ∧ 0 ≤ d.w2 12435 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12435 ≤ 2 * (228 / 100 : ℝ) / 12435 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12435 ≤ 2 * (370 / 100 : ℝ) / 12435 := by
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
    (completeRAData (tableEnvelope C) 12435 161).locationBound 12435 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12435 161).energyBound 12435 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12435 161) (d.f1 12435 161) d.f2 ≤
      32 * (((4830788237 / 1000000000000000000) : ℝ) + (161163273 / 100000000000000000) + (387356487 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12435 161) (d.w1 12435 161)
      (d.w2 12435 161) ≤
      32 * (((1952922423 / 100000000000000000000) : ℝ) + (1389466959 / 100000000000000000000) + (253838407 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12435 161) (d.f1 12435 161) d.f2 ≤
      ((4830788237 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4830788237 / 1000000000000000000)) * ((161163273 / 100000000000000000)) * (126 / 100) +
      2 * (((161163273 / 100000000000000000)) ^ 2 + 2 * ((4830788237 / 1000000000000000000)) * ((387356487 / 1000000000000000000))) +
      6 * ((161163273 / 100000000000000000)) * ((387356487 / 1000000000000000000)) * (126 / 100) + 8 * ((387356487 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12435 161) (d.f1 12435 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12435 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12435 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12435 161) (d.f1 12435 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12435 161) (d.w1 12435 161) (d.w2 12435 161)
  have hwexpr0 : 0 ≤ d.w0 12435 161 + d.w1 12435 161 * √(π / 2) +
      2 * d.w2 12435 161 + energyR16 12435 *
      radiusPolynomialRoot16 (d.w0 12435 161) (d.w1 12435 161) (d.w2 12435 161) := by
    positivity
  constructor
  · change (12435 : ℝ) ^ 8 * (mA 12435 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12435 161) (d.f1 12435 161) d.f2 + locationR16 12435 *
        radiusPolynomialRoot16 (d.f0 12435 161) (d.f1 12435 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12435 : ℝ) ^ 8 * (mA 12435 : ℝ) ^ 8 *
        ((((4830788237 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4830788237 / 1000000000000000000)) * ((161163273 / 100000000000000000)) * (126 / 100) +
          2 * (((161163273 / 100000000000000000)) ^ 2 + 2 * ((4830788237 / 1000000000000000000)) * ((387356487 / 1000000000000000000))) +
          6 * ((161163273 / 100000000000000000)) * ((387356487 / 1000000000000000000)) * (126 / 100) + 8 * ((387356487 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12435) *
          (32 * (((4830788237 / 1000000000000000000) : ℝ) + (161163273 / 100000000000000000) + (387356487 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12435 : ℝ) ^ 16 *
      (d.w0 12435 161 + d.w1 12435 161 * √(π / 2) + 2 * d.w2 12435 161 +
        energyR16 12435 * radiusPolynomialRoot16 (d.w0 12435 161) (d.w1 12435 161)
          (d.w2 12435 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12435 : ℝ) ^ 16 *
        (((1952922423 / 100000000000000000000) : ℝ) + ((1389466959 / 100000000000000000000)) * (126 / 100) + 2 * ((253838407 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12435) *
          (32 * (((1952922423 / 100000000000000000000) : ℝ) + (1389466959 / 100000000000000000000) + (253838407 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12435

/-! A coarse bound on the actual paper statistics constant at dimension 12436. -/
namespace BstLean.Part266.Row12436
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12434 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12434 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12434 128 ≤ (12688 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12688 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12436) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12436 : ℕ))
    (by norm_num : (12436 : ℕ) ≤ 16384)
  have ht : paperTail256 12436 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12436 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12436 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12436 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12436 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12436 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12434 128 * √(2 / (12436 : ℝ)) *
      (√(12436 : ℝ) + paperT0 12436 + paperTail256 12436) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12436 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12436 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12436 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12434 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12434 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12436 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12436

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12436
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12436 (61 / 100) 161 (17 / (100 * 12436)) (26 / (10 * 12436)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12436 (61 / 100) 161 (17 / (100 * 12436)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (126887119 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (816256809 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (94659539 / 15625000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12436 / 12436 * (61 / 100)) ^ 4 * inverseRadius8 (12436 - 1) /
            envelopeGap 12436 (61 / 100) 161 (17 / (100 * 12436)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12436

namespace BstLean.Part266.Row12436
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12436 161 ≤ (2414907303 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12436 161 ≤ (322261633 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (387278547 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12436 161 ≤ (1952450803 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12436 161 ≤ (138913153 / 10000000000000000000)
  w2 : (tableEnvelope C).w2 12436 161 ≤ (101510869 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (126887119 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (126887119 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (816256809 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (94659539 / 15625000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((739459 / 200000000) : ℝ) ≤ √(17 / (100 * 12436) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12436) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (450576731 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1262636757 / 31250000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12436) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12436) ≤ (3553729 / 31250000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12436) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12436 * (161 : ℝ) ^ 2 + 26 / (10 * 12436) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12436) : ℝ)) (tA 12436 * 161 ^ 2 + 26 / (10 * 12436)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((739459 / 200000000))) * ((126887119 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((739459 / 200000000)) ^ 3) * ((816256809 / 500000000000000000000000))) + ((94659539 / 15625000000000000000000)) * (3 / 2 * (39895 / 100000) / ((739459 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12436) : ℝ)) d.D d.V d.P (√(tA 12436) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((739459 / 200000000)) ^ 2 * (((450576731 / 200000000000000)) * ((1262636757 / 31250000000000000)))) + ((94659539 / 15625000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12436) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((739459 / 200000000)) * ((126887119 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12436) : ℝ)) (tA 12436 * 161 ^ 2 + 26 / (10 * 12436)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((126887119 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((739459 / 200000000)) ^ 2) * ((816256809 / 500000000000000000000000)) + ((94659539 / 15625000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12436) : ℝ)) (√(26 / (10 * 12436) : ℝ)) d.D d.V d.P (√(tA 12436) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((739459 / 200000000)) * (((450576731 / 200000000000000)) * ((1262636757 / 31250000000000000))) + ((94659539 / 15625000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12436) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((126887119 / 25000000000000000000) : ℝ) + ((94659539 / 15625000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12436

namespace BstLean.Part266.Row12436
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12436 161 ∧
    0 ≤ (tableEnvelope C).f1 12436 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12436 161 ∧
    0 ≤ (tableEnvelope C).w1 12436 161 ∧ 0 ≤ (tableEnvelope C).w2 12436 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12436 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12436 161 ∧ 0 ≤ d.f1 12436 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12436 161 ∧ 0 ≤ d.w1 12436 161 ∧ 0 ≤ d.w2 12436 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12436 ≤ 2 * (228 / 100 : ℝ) / 12436 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12436 ≤ 2 * (370 / 100 : ℝ) / 12436 := by
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
    (completeRAData (tableEnvelope C) 12436 161).locationBound 12436 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12436 161).energyBound 12436 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12436 161) (d.f1 12436 161) d.f2 ≤
      32 * (((2414907303 / 500000000000000000) : ℝ) + (322261633 / 200000000000000000) + (387278547 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12436 161) (d.w1 12436 161)
      (d.w2 12436 161) ≤
      32 * (((1952450803 / 100000000000000000000) : ℝ) + (138913153 / 10000000000000000000) + (101510869 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12436 161) (d.f1 12436 161) d.f2 ≤
      ((2414907303 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2414907303 / 500000000000000000)) * ((322261633 / 200000000000000000)) * (126 / 100) +
      2 * (((322261633 / 200000000000000000)) ^ 2 + 2 * ((2414907303 / 500000000000000000)) * ((387278547 / 1000000000000000000))) +
      6 * ((322261633 / 200000000000000000)) * ((387278547 / 1000000000000000000)) * (126 / 100) + 8 * ((387278547 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12436 161) (d.f1 12436 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12436 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12436 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12436 161) (d.f1 12436 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12436 161) (d.w1 12436 161) (d.w2 12436 161)
  have hwexpr0 : 0 ≤ d.w0 12436 161 + d.w1 12436 161 * √(π / 2) +
      2 * d.w2 12436 161 + energyR16 12436 *
      radiusPolynomialRoot16 (d.w0 12436 161) (d.w1 12436 161) (d.w2 12436 161) := by
    positivity
  constructor
  · change (12436 : ℝ) ^ 8 * (mA 12436 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12436 161) (d.f1 12436 161) d.f2 + locationR16 12436 *
        radiusPolynomialRoot16 (d.f0 12436 161) (d.f1 12436 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12436 : ℝ) ^ 8 * (mA 12436 : ℝ) ^ 8 *
        ((((2414907303 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2414907303 / 500000000000000000)) * ((322261633 / 200000000000000000)) * (126 / 100) +
          2 * (((322261633 / 200000000000000000)) ^ 2 + 2 * ((2414907303 / 500000000000000000)) * ((387278547 / 1000000000000000000))) +
          6 * ((322261633 / 200000000000000000)) * ((387278547 / 1000000000000000000)) * (126 / 100) + 8 * ((387278547 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12436) *
          (32 * (((2414907303 / 500000000000000000) : ℝ) + (322261633 / 200000000000000000) + (387278547 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12436 : ℝ) ^ 16 *
      (d.w0 12436 161 + d.w1 12436 161 * √(π / 2) + 2 * d.w2 12436 161 +
        energyR16 12436 * radiusPolynomialRoot16 (d.w0 12436 161) (d.w1 12436 161)
          (d.w2 12436 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12436 : ℝ) ^ 16 *
        (((1952450803 / 100000000000000000000) : ℝ) + ((138913153 / 10000000000000000000)) * (126 / 100) + 2 * ((101510869 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12436) *
          (32 * (((1952450803 / 100000000000000000000) : ℝ) + (138913153 / 10000000000000000000) + (101510869 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12436

/-! A coarse bound on the actual paper statistics constant at dimension 12437. -/
namespace BstLean.Part266.Row12437
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12435 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12435 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12435 128 ≤ (12689 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12689 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12437) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12437 : ℕ))
    (by norm_num : (12437 : ℕ) ≤ 16384)
  have ht : paperTail256 12437 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12437 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12437 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12437 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12437 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12437 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12435 128 * √(2 / (12437 : ℝ)) *
      (√(12437 : ℝ) + paperT0 12437 + paperTail256 12437) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12437 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12437 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12437 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12435 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12435 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12437 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12437

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12437
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12437 (61 / 100) 161 (17 / (100 * 12437)) (26 / (10 * 12437)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12437 (61 / 100) 161 (17 / (100 * 12437)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (507426051 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (163198861 / 100000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1210855219 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12437 / 12437 * (61 / 100)) ^ 4 * inverseRadius8 (12437 - 1) /
            envelopeGap 12437 (61 / 100) 161 (17 / (100 * 12437)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12437

namespace BstLean.Part266.Row12437
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12437 161 ≤ (4828845089 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12437 161 ≤ (1610984581 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (12100023 / 31250000000000000)
  w0 : (tableEnvelope C).w0 12437 161 ≤ (487995033 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12437 161 ≤ (1388796593 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12437 161 ≤ (126857979 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (507426051 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (507426051 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (163198861 / 100000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1210855219 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1848573 / 500000000) : ℝ) ≤ √(17 / (100 * 12437) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12437) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2252611931 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40397878781 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12437) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12437) ≤ (22742037 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12437) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12437 * (161 : ℝ) ^ 2 + 26 / (10 * 12437) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12437) : ℝ)) (tA 12437 * 161 ^ 2 + 26 / (10 * 12437)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1848573 / 500000000))) * ((507426051 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1848573 / 500000000)) ^ 3) * ((163198861 / 100000000000000000000000))) + ((1210855219 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1848573 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12437) : ℝ)) d.D d.V d.P (√(tA 12437) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1848573 / 500000000)) ^ 2 * (((2252611931 / 1000000000000000)) * ((40397878781 / 1000000000000000000)))) + ((1210855219 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12437) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1848573 / 500000000)) * ((507426051 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12437) : ℝ)) (tA 12437 * 161 ^ 2 + 26 / (10 * 12437)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((507426051 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1848573 / 500000000)) ^ 2) * ((163198861 / 100000000000000000000000)) + ((1210855219 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12437) : ℝ)) (√(26 / (10 * 12437) : ℝ)) d.D d.V d.P (√(tA 12437) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1848573 / 500000000)) * (((2252611931 / 1000000000000000)) * ((40397878781 / 1000000000000000000))) + ((1210855219 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12437) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((507426051 / 100000000000000000000) : ℝ) + ((1210855219 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12437

namespace BstLean.Part266.Row12437
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12437 161 ∧
    0 ≤ (tableEnvelope C).f1 12437 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12437 161 ∧
    0 ≤ (tableEnvelope C).w1 12437 161 ∧ 0 ≤ (tableEnvelope C).w2 12437 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12437 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12437 161 ∧ 0 ≤ d.f1 12437 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12437 161 ∧ 0 ≤ d.w1 12437 161 ∧ 0 ≤ d.w2 12437 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12437 ≤ 2 * (228 / 100 : ℝ) / 12437 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12437 ≤ 2 * (370 / 100 : ℝ) / 12437 := by
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
    (completeRAData (tableEnvelope C) 12437 161).locationBound 12437 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12437 161).energyBound 12437 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12437 161) (d.f1 12437 161) d.f2 ≤
      32 * (((4828845089 / 1000000000000000000) : ℝ) + (1610984581 / 1000000000000000000) + (12100023 / 31250000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12437 161) (d.w1 12437 161)
      (d.w2 12437 161) ≤
      32 * (((487995033 / 25000000000000000000) : ℝ) + (1388796593 / 100000000000000000000) + (126857979 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12437 161) (d.f1 12437 161) d.f2 ≤
      ((4828845089 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4828845089 / 1000000000000000000)) * ((1610984581 / 1000000000000000000)) * (126 / 100) +
      2 * (((1610984581 / 1000000000000000000)) ^ 2 + 2 * ((4828845089 / 1000000000000000000)) * ((12100023 / 31250000000000000))) +
      6 * ((1610984581 / 1000000000000000000)) * ((12100023 / 31250000000000000)) * (126 / 100) + 8 * ((12100023 / 31250000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12437 161) (d.f1 12437 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12437 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12437 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12437 161) (d.f1 12437 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12437 161) (d.w1 12437 161) (d.w2 12437 161)
  have hwexpr0 : 0 ≤ d.w0 12437 161 + d.w1 12437 161 * √(π / 2) +
      2 * d.w2 12437 161 + energyR16 12437 *
      radiusPolynomialRoot16 (d.w0 12437 161) (d.w1 12437 161) (d.w2 12437 161) := by
    positivity
  constructor
  · change (12437 : ℝ) ^ 8 * (mA 12437 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12437 161) (d.f1 12437 161) d.f2 + locationR16 12437 *
        radiusPolynomialRoot16 (d.f0 12437 161) (d.f1 12437 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12437 : ℝ) ^ 8 * (mA 12437 : ℝ) ^ 8 *
        ((((4828845089 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4828845089 / 1000000000000000000)) * ((1610984581 / 1000000000000000000)) * (126 / 100) +
          2 * (((1610984581 / 1000000000000000000)) ^ 2 + 2 * ((4828845089 / 1000000000000000000)) * ((12100023 / 31250000000000000))) +
          6 * ((1610984581 / 1000000000000000000)) * ((12100023 / 31250000000000000)) * (126 / 100) + 8 * ((12100023 / 31250000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12437) *
          (32 * (((4828845089 / 1000000000000000000) : ℝ) + (1610984581 / 1000000000000000000) + (12100023 / 31250000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12437 : ℝ) ^ 16 *
      (d.w0 12437 161 + d.w1 12437 161 * √(π / 2) + 2 * d.w2 12437 161 +
        energyR16 12437 * radiusPolynomialRoot16 (d.w0 12437 161) (d.w1 12437 161)
          (d.w2 12437 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12437 : ℝ) ^ 16 *
        (((487995033 / 25000000000000000000) : ℝ) + ((1388796593 / 100000000000000000000)) * (126 / 100) + 2 * ((126857979 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12437) *
          (32 * (((487995033 / 25000000000000000000) : ℝ) + (1388796593 / 100000000000000000000) + (126857979 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12437

/-! A coarse bound on the actual paper statistics constant at dimension 12438. -/
namespace BstLean.Part266.Row12438
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12436 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12436 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12436 128 ≤ (12690 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12690 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12438) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12438 : ℕ))
    (by norm_num : (12438 : ℕ) ≤ 16384)
  have ht : paperTail256 12438 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12438 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12438 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12438 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12438 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12438 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12436 128 * √(2 / (12438 : ℝ)) *
      (√(12438 : ℝ) + paperT0 12438 + paperTail256 12438) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12438 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12438 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12438 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12436 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12436 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12438 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12438

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12438
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12438 (61 / 100) 161 (17 / (100 * 12438)) (26 / (10 * 12438)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12438 (61 / 100) 161 (17 / (100 * 12438)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (101460733 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1631463813 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6050344571 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12438 / 12438 * (61 / 100)) ^ 4 * inverseRadius8 (12438 - 1) /
            envelopeGap 12438 (61 / 100) 161 (17 / (100 * 12438)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12438

namespace BstLean.Part266.Row12438
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12438 161 ≤ (4827875913 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12438 161 ≤ (805330551 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (387122949 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12438 161 ≤ (1951509627 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12438 161 ≤ (1388461769 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12438 161 ≤ (253654763 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (101460733 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (101460733 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1631463813 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6050344571 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3696997 / 1000000000) : ℝ) ≤ √(17 / (100 * 12438) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12438) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2252340261 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (20195691453 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12438) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12438) ≤ (113701043 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12438) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12438 * (161 : ℝ) ^ 2 + 26 / (10 * 12438) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12438) : ℝ)) (tA 12438 * 161 ^ 2 + 26 / (10 * 12438)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3696997 / 1000000000))) * ((101460733 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3696997 / 1000000000)) ^ 3) * ((1631463813 / 1000000000000000000000000))) + ((6050344571 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3696997 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12438) : ℝ)) d.D d.V d.P (√(tA 12438) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3696997 / 1000000000)) ^ 2 * (((2252340261 / 1000000000000000)) * ((20195691453 / 500000000000000000)))) + ((6050344571 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12438) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3696997 / 1000000000)) * ((101460733 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12438) : ℝ)) (tA 12438 * 161 ^ 2 + 26 / (10 * 12438)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((101460733 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3696997 / 1000000000)) ^ 2) * ((1631463813 / 1000000000000000000000000)) + ((6050344571 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12438) : ℝ)) (√(26 / (10 * 12438) : ℝ)) d.D d.V d.P (√(tA 12438) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3696997 / 1000000000)) * (((2252340261 / 1000000000000000)) * ((20195691453 / 500000000000000000))) + ((6050344571 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12438) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((101460733 / 20000000000000000000) : ℝ) + ((6050344571 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12438

namespace BstLean.Part266.Row12438
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12438 161 ∧
    0 ≤ (tableEnvelope C).f1 12438 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12438 161 ∧
    0 ≤ (tableEnvelope C).w1 12438 161 ∧ 0 ≤ (tableEnvelope C).w2 12438 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12438 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12438 161 ∧ 0 ≤ d.f1 12438 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12438 161 ∧ 0 ≤ d.w1 12438 161 ∧ 0 ≤ d.w2 12438 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12438 ≤ 2 * (228 / 100 : ℝ) / 12438 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12438 ≤ 2 * (370 / 100 : ℝ) / 12438 := by
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
    (completeRAData (tableEnvelope C) 12438 161).locationBound 12438 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12438 161).energyBound 12438 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12438 161) (d.f1 12438 161) d.f2 ≤
      32 * (((4827875913 / 1000000000000000000) : ℝ) + (805330551 / 500000000000000000) + (387122949 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12438 161) (d.w1 12438 161)
      (d.w2 12438 161) ≤
      32 * (((1951509627 / 100000000000000000000) : ℝ) + (1388461769 / 100000000000000000000) + (253654763 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12438 161) (d.f1 12438 161) d.f2 ≤
      ((4827875913 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4827875913 / 1000000000000000000)) * ((805330551 / 500000000000000000)) * (126 / 100) +
      2 * (((805330551 / 500000000000000000)) ^ 2 + 2 * ((4827875913 / 1000000000000000000)) * ((387122949 / 1000000000000000000))) +
      6 * ((805330551 / 500000000000000000)) * ((387122949 / 1000000000000000000)) * (126 / 100) + 8 * ((387122949 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12438 161) (d.f1 12438 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12438 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12438 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12438 161) (d.f1 12438 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12438 161) (d.w1 12438 161) (d.w2 12438 161)
  have hwexpr0 : 0 ≤ d.w0 12438 161 + d.w1 12438 161 * √(π / 2) +
      2 * d.w2 12438 161 + energyR16 12438 *
      radiusPolynomialRoot16 (d.w0 12438 161) (d.w1 12438 161) (d.w2 12438 161) := by
    positivity
  constructor
  · change (12438 : ℝ) ^ 8 * (mA 12438 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12438 161) (d.f1 12438 161) d.f2 + locationR16 12438 *
        radiusPolynomialRoot16 (d.f0 12438 161) (d.f1 12438 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12438 : ℝ) ^ 8 * (mA 12438 : ℝ) ^ 8 *
        ((((4827875913 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4827875913 / 1000000000000000000)) * ((805330551 / 500000000000000000)) * (126 / 100) +
          2 * (((805330551 / 500000000000000000)) ^ 2 + 2 * ((4827875913 / 1000000000000000000)) * ((387122949 / 1000000000000000000))) +
          6 * ((805330551 / 500000000000000000)) * ((387122949 / 1000000000000000000)) * (126 / 100) + 8 * ((387122949 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12438) *
          (32 * (((4827875913 / 1000000000000000000) : ℝ) + (805330551 / 500000000000000000) + (387122949 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12438 : ℝ) ^ 16 *
      (d.w0 12438 161 + d.w1 12438 161 * √(π / 2) + 2 * d.w2 12438 161 +
        energyR16 12438 * radiusPolynomialRoot16 (d.w0 12438 161) (d.w1 12438 161)
          (d.w2 12438 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12438 : ℝ) ^ 16 *
        (((1951509627 / 100000000000000000000) : ℝ) + ((1388461769 / 100000000000000000000)) * (126 / 100) + 2 * ((253654763 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12438) *
          (32 * (((1951509627 / 100000000000000000000) : ℝ) + (1388461769 / 100000000000000000000) + (253654763 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12438

/-! A coarse bound on the actual paper statistics constant at dimension 12439. -/
namespace BstLean.Part266.Row12439
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12437 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12437 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12437 128 ≤ (12691 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12691 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12439) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12439 : ℕ))
    (by norm_num : (12439 : ℕ) ≤ 16384)
  have ht : paperTail256 12439 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12439 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12439 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12439 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12439 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12439 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12437 128 * √(2 / (12439 : ℝ)) *
      (√(12439 : ℝ) + paperT0 12439 + paperTail256 12439) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12439 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12439 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12439 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12437 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12437 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12439 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12439

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12439
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12439 (61 / 100) 161 (17 / (100 * 12439)) (26 / (10 * 12439)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12439 (61 / 100) 161 (17 / (100 * 12439)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (253590659 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (815469613 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3023207961 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12439 / 12439 * (61 / 100)) ^ 4 * inverseRadius8 (12439 - 1) /
            envelopeGap 12439 (61 / 100) 161 (17 / (100 * 12439)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12439

namespace BstLean.Part266.Row12439
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12439 161 ≤ (965380661 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12439 161 ≤ (805168429 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (9676127 / 25000000000000000)
  w0 : (tableEnvelope C).w0 12439 161 ≤ (243879813 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 12439 161 ≤ (347031671 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12439 161 ≤ (63398397 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (253590659 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (253590659 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (815469613 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3023207961 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3696849 / 1000000000) : ℝ) ≤ √(17 / (100 * 12439) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12439) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (450413729 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (8076977717 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12439) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12439) ≤ (56845951 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12439) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12439 * (161 : ℝ) ^ 2 + 26 / (10 * 12439) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12439) : ℝ)) (tA 12439 * 161 ^ 2 + 26 / (10 * 12439)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3696849 / 1000000000))) * ((253590659 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3696849 / 1000000000)) ^ 3) * ((815469613 / 500000000000000000000000))) + ((3023207961 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3696849 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12439) : ℝ)) d.D d.V d.P (√(tA 12439) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3696849 / 1000000000)) ^ 2 * (((450413729 / 200000000000000)) * ((8076977717 / 200000000000000000)))) + ((3023207961 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12439) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3696849 / 1000000000)) * ((253590659 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12439) : ℝ)) (tA 12439 * 161 ^ 2 + 26 / (10 * 12439)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((253590659 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3696849 / 1000000000)) ^ 2) * ((815469613 / 500000000000000000000000)) + ((3023207961 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12439) : ℝ)) (√(26 / (10 * 12439) : ℝ)) d.D d.V d.P (√(tA 12439) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3696849 / 1000000000)) * (((450413729 / 200000000000000)) * ((8076977717 / 200000000000000000))) + ((3023207961 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12439) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((253590659 / 50000000000000000000) : ℝ) + ((3023207961 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12439

namespace BstLean.Part266.Row12439
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12439 161 ∧
    0 ≤ (tableEnvelope C).f1 12439 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12439 161 ∧
    0 ≤ (tableEnvelope C).w1 12439 161 ∧ 0 ≤ (tableEnvelope C).w2 12439 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12439 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12439 161 ∧ 0 ≤ d.f1 12439 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12439 161 ∧ 0 ≤ d.w1 12439 161 ∧ 0 ≤ d.w2 12439 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12439 ≤ 2 * (228 / 100 : ℝ) / 12439 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12439 ≤ 2 * (370 / 100 : ℝ) / 12439 := by
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
    (completeRAData (tableEnvelope C) 12439 161).locationBound 12439 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12439 161).energyBound 12439 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12439 161) (d.f1 12439 161) d.f2 ≤
      32 * (((965380661 / 200000000000000000) : ℝ) + (805168429 / 500000000000000000) + (9676127 / 25000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12439 161) (d.w1 12439 161)
      (d.w2 12439 161) ≤
      32 * (((243879813 / 12500000000000000000) : ℝ) + (347031671 / 25000000000000000000) + (63398397 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12439 161) (d.f1 12439 161) d.f2 ≤
      ((965380661 / 200000000000000000) : ℝ) ^ 2 + 2 * ((965380661 / 200000000000000000)) * ((805168429 / 500000000000000000)) * (126 / 100) +
      2 * (((805168429 / 500000000000000000)) ^ 2 + 2 * ((965380661 / 200000000000000000)) * ((9676127 / 25000000000000000))) +
      6 * ((805168429 / 500000000000000000)) * ((9676127 / 25000000000000000)) * (126 / 100) + 8 * ((9676127 / 25000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12439 161) (d.f1 12439 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12439 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12439 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12439 161) (d.f1 12439 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12439 161) (d.w1 12439 161) (d.w2 12439 161)
  have hwexpr0 : 0 ≤ d.w0 12439 161 + d.w1 12439 161 * √(π / 2) +
      2 * d.w2 12439 161 + energyR16 12439 *
      radiusPolynomialRoot16 (d.w0 12439 161) (d.w1 12439 161) (d.w2 12439 161) := by
    positivity
  constructor
  · change (12439 : ℝ) ^ 8 * (mA 12439 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12439 161) (d.f1 12439 161) d.f2 + locationR16 12439 *
        radiusPolynomialRoot16 (d.f0 12439 161) (d.f1 12439 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12439 : ℝ) ^ 8 * (mA 12439 : ℝ) ^ 8 *
        ((((965380661 / 200000000000000000) : ℝ) ^ 2 + 2 * ((965380661 / 200000000000000000)) * ((805168429 / 500000000000000000)) * (126 / 100) +
          2 * (((805168429 / 500000000000000000)) ^ 2 + 2 * ((965380661 / 200000000000000000)) * ((9676127 / 25000000000000000))) +
          6 * ((805168429 / 500000000000000000)) * ((9676127 / 25000000000000000)) * (126 / 100) + 8 * ((9676127 / 25000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12439) *
          (32 * (((965380661 / 200000000000000000) : ℝ) + (805168429 / 500000000000000000) + (9676127 / 25000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12439 : ℝ) ^ 16 *
      (d.w0 12439 161 + d.w1 12439 161 * √(π / 2) + 2 * d.w2 12439 161 +
        energyR16 12439 * radiusPolynomialRoot16 (d.w0 12439 161) (d.w1 12439 161)
          (d.w2 12439 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12439 : ℝ) ^ 16 *
        (((243879813 / 12500000000000000000) : ℝ) + ((347031671 / 25000000000000000000)) * (126 / 100) + 2 * ((63398397 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12439) *
          (32 * (((243879813 / 12500000000000000000) : ℝ) + (347031671 / 25000000000000000000) + (63398397 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12439

/-! A coarse bound on the actual paper statistics constant at dimension 12440. -/
namespace BstLean.Part266.Row12440
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12438 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12438 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12438 128 ≤ (12692 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12692 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12440) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12440 : ℕ))
    (by norm_num : (12440 : ℕ) ≤ 16384)
  have ht : paperTail256 12440 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12440 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12440 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12440 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12440 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12440 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12438 128 * √(2 / (12440 : ℝ)) *
      (√(12440 : ℝ) + paperT0 12440 + paperTail256 12440) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12440 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12440 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12440 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12438 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12438 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12440 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12440

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12440
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12440 (61 / 100) 161 (17 / (100 * 12440)) (26 / (10 * 12440)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12440 (61 / 100) 161 (17 / (100 * 12440)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (507059011 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1630414851 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3021245073 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12440 / 12440 * (61 / 100)) ^ 4 * inverseRadius8 (12440 - 1) /
            envelopeGap 12440 (61 / 100) 161 (17 / (100 * 12440)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12440

namespace BstLean.Part266.Row12440
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12440 161 ≤ (482593481 / 100000000000000000)
  f1 : (tableEnvelope C).f1 12440 161 ≤ (805006797 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (386967341 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12440 161 ≤ (1950568329 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12440 161 ≤ (138779209 / 10000000000000000000)
  w2 : (tableEnvelope C).w2 12440 161 ≤ (101412973 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (507059011 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (507059011 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1630414851 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3021245073 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((36967 / 10000000) : ℝ) ≤ √(17 / (100 * 12440) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12440) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (450359417 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (8075679169 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12440) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12440) ≤ (113682763 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12440) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12440 * (161 : ℝ) ^ 2 + 26 / (10 * 12440) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12440) : ℝ)) (tA 12440 * 161 ^ 2 + 26 / (10 * 12440)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((36967 / 10000000))) * ((507059011 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((36967 / 10000000)) ^ 3) * ((1630414851 / 1000000000000000000000000))) + ((3021245073 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((36967 / 10000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12440) : ℝ)) d.D d.V d.P (√(tA 12440) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((36967 / 10000000)) ^ 2 * (((450359417 / 200000000000000)) * ((8075679169 / 200000000000000000)))) + ((3021245073 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12440) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((36967 / 10000000)) * ((507059011 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12440) : ℝ)) (tA 12440 * 161 ^ 2 + 26 / (10 * 12440)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((507059011 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((36967 / 10000000)) ^ 2) * ((1630414851 / 1000000000000000000000000)) + ((3021245073 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12440) : ℝ)) (√(26 / (10 * 12440) : ℝ)) d.D d.V d.P (√(tA 12440) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((36967 / 10000000)) * (((450359417 / 200000000000000)) * ((8075679169 / 200000000000000000))) + ((3021245073 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12440) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((507059011 / 100000000000000000000) : ℝ) + ((3021245073 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12440

namespace BstLean.Part266.Row12440
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12440 161 ∧
    0 ≤ (tableEnvelope C).f1 12440 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12440 161 ∧
    0 ≤ (tableEnvelope C).w1 12440 161 ∧ 0 ≤ (tableEnvelope C).w2 12440 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12440 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12440 161 ∧ 0 ≤ d.f1 12440 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12440 161 ∧ 0 ≤ d.w1 12440 161 ∧ 0 ≤ d.w2 12440 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12440 ≤ 2 * (228 / 100 : ℝ) / 12440 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12440 ≤ 2 * (370 / 100 : ℝ) / 12440 := by
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
    (completeRAData (tableEnvelope C) 12440 161).locationBound 12440 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12440 161).energyBound 12440 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12440 161) (d.f1 12440 161) d.f2 ≤
      32 * (((482593481 / 100000000000000000) : ℝ) + (805006797 / 500000000000000000) + (386967341 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12440 161) (d.w1 12440 161)
      (d.w2 12440 161) ≤
      32 * (((1950568329 / 100000000000000000000) : ℝ) + (138779209 / 10000000000000000000) + (101412973 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12440 161) (d.f1 12440 161) d.f2 ≤
      ((482593481 / 100000000000000000) : ℝ) ^ 2 + 2 * ((482593481 / 100000000000000000)) * ((805006797 / 500000000000000000)) * (126 / 100) +
      2 * (((805006797 / 500000000000000000)) ^ 2 + 2 * ((482593481 / 100000000000000000)) * ((386967341 / 1000000000000000000))) +
      6 * ((805006797 / 500000000000000000)) * ((386967341 / 1000000000000000000)) * (126 / 100) + 8 * ((386967341 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12440 161) (d.f1 12440 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12440 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12440 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12440 161) (d.f1 12440 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12440 161) (d.w1 12440 161) (d.w2 12440 161)
  have hwexpr0 : 0 ≤ d.w0 12440 161 + d.w1 12440 161 * √(π / 2) +
      2 * d.w2 12440 161 + energyR16 12440 *
      radiusPolynomialRoot16 (d.w0 12440 161) (d.w1 12440 161) (d.w2 12440 161) := by
    positivity
  constructor
  · change (12440 : ℝ) ^ 8 * (mA 12440 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12440 161) (d.f1 12440 161) d.f2 + locationR16 12440 *
        radiusPolynomialRoot16 (d.f0 12440 161) (d.f1 12440 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12440 : ℝ) ^ 8 * (mA 12440 : ℝ) ^ 8 *
        ((((482593481 / 100000000000000000) : ℝ) ^ 2 + 2 * ((482593481 / 100000000000000000)) * ((805006797 / 500000000000000000)) * (126 / 100) +
          2 * (((805006797 / 500000000000000000)) ^ 2 + 2 * ((482593481 / 100000000000000000)) * ((386967341 / 1000000000000000000))) +
          6 * ((805006797 / 500000000000000000)) * ((386967341 / 1000000000000000000)) * (126 / 100) + 8 * ((386967341 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12440) *
          (32 * (((482593481 / 100000000000000000) : ℝ) + (805006797 / 500000000000000000) + (386967341 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12440 : ℝ) ^ 16 *
      (d.w0 12440 161 + d.w1 12440 161 * √(π / 2) + 2 * d.w2 12440 161 +
        energyR16 12440 * radiusPolynomialRoot16 (d.w0 12440 161) (d.w1 12440 161)
          (d.w2 12440 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12440 : ℝ) ^ 16 *
        (((1950568329 / 100000000000000000000) : ℝ) + ((138779209 / 10000000000000000000)) * (126 / 100) + 2 * ((101412973 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12440) *
          (32 * (((1950568329 / 100000000000000000000) : ℝ) + (138779209 / 10000000000000000000) + (101412973 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12440

/-! A coarse bound on the actual paper statistics constant at dimension 12441. -/
namespace BstLean.Part266.Row12441
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12439 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12439 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12439 128 ≤ (12693 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12693 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12441) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12441 : ℕ))
    (by norm_num : (12441 : ℕ) ≤ 16384)
  have ht : paperTail256 12441 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12441 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12441 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12441 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12441 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12441 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12439 128 * √(2 / (12441 : ℝ)) *
      (√(12441 : ℝ) + paperT0 12441 + paperTail256 12441) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12441 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12441 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12441 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12439 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12439 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12441 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12441

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12441
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12441 (61 / 100) 161 (17 / (100 * 12441)) (26 / (10 * 12441)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12441 (61 / 100) 161 (17 / (100 * 12441)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (506936743 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (814945343 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (150964181 / 25000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12441 / 12441 * (61 / 100)) ^ 4 * inverseRadius8 (12441 - 1) /
            envelopeGap 12441 (61 / 100) 161 (17 / (100 * 12441)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12441

namespace BstLean.Part266.Row12441
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12441 161 ≤ (4824966653 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12441 161 ≤ (321938087 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (3095117 / 8000000000000000)
  w0 : (tableEnvelope C).w0 12441 161 ≤ (975049159 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12441 161 ≤ (138745761 / 10000000000000000000)
  w2 : (tableEnvelope C).w2 12441 161 ≤ (506942593 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (506936743 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (506936743 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (814945343 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (150964181 / 25000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3696551 / 1000000000) : ℝ) ≤ √(17 / (100 * 12441) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12441) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2251525579 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (20185952331 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12441) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12441) ≤ (909389 / 8000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12441) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12441 * (161 : ℝ) ^ 2 + 26 / (10 * 12441) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12441) : ℝ)) (tA 12441 * 161 ^ 2 + 26 / (10 * 12441)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3696551 / 1000000000))) * ((506936743 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3696551 / 1000000000)) ^ 3) * ((814945343 / 500000000000000000000000))) + ((150964181 / 25000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3696551 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12441) : ℝ)) d.D d.V d.P (√(tA 12441) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3696551 / 1000000000)) ^ 2 * (((2251525579 / 1000000000000000)) * ((20185952331 / 500000000000000000)))) + ((150964181 / 25000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12441) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3696551 / 1000000000)) * ((506936743 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12441) : ℝ)) (tA 12441 * 161 ^ 2 + 26 / (10 * 12441)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((506936743 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3696551 / 1000000000)) ^ 2) * ((814945343 / 500000000000000000000000)) + ((150964181 / 25000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12441) : ℝ)) (√(26 / (10 * 12441) : ℝ)) d.D d.V d.P (√(tA 12441) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3696551 / 1000000000)) * (((2251525579 / 1000000000000000)) * ((20185952331 / 500000000000000000))) + ((150964181 / 25000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12441) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((506936743 / 100000000000000000000) : ℝ) + ((150964181 / 25000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12441

namespace BstLean.Part266.Row12441
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12441 161 ∧
    0 ≤ (tableEnvelope C).f1 12441 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12441 161 ∧
    0 ≤ (tableEnvelope C).w1 12441 161 ∧ 0 ≤ (tableEnvelope C).w2 12441 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12441 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12441 161 ∧ 0 ≤ d.f1 12441 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12441 161 ∧ 0 ≤ d.w1 12441 161 ∧ 0 ≤ d.w2 12441 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12441 ≤ 2 * (228 / 100 : ℝ) / 12441 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12441 ≤ 2 * (370 / 100 : ℝ) / 12441 := by
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
    (completeRAData (tableEnvelope C) 12441 161).locationBound 12441 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12441 161).energyBound 12441 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12441 161) (d.f1 12441 161) d.f2 ≤
      32 * (((4824966653 / 1000000000000000000) : ℝ) + (321938087 / 200000000000000000) + (3095117 / 8000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12441 161) (d.w1 12441 161)
      (d.w2 12441 161) ≤
      32 * (((975049159 / 50000000000000000000) : ℝ) + (138745761 / 10000000000000000000) + (506942593 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12441 161) (d.f1 12441 161) d.f2 ≤
      ((4824966653 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4824966653 / 1000000000000000000)) * ((321938087 / 200000000000000000)) * (126 / 100) +
      2 * (((321938087 / 200000000000000000)) ^ 2 + 2 * ((4824966653 / 1000000000000000000)) * ((3095117 / 8000000000000000))) +
      6 * ((321938087 / 200000000000000000)) * ((3095117 / 8000000000000000)) * (126 / 100) + 8 * ((3095117 / 8000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12441 161) (d.f1 12441 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12441 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12441 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12441 161) (d.f1 12441 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12441 161) (d.w1 12441 161) (d.w2 12441 161)
  have hwexpr0 : 0 ≤ d.w0 12441 161 + d.w1 12441 161 * √(π / 2) +
      2 * d.w2 12441 161 + energyR16 12441 *
      radiusPolynomialRoot16 (d.w0 12441 161) (d.w1 12441 161) (d.w2 12441 161) := by
    positivity
  constructor
  · change (12441 : ℝ) ^ 8 * (mA 12441 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12441 161) (d.f1 12441 161) d.f2 + locationR16 12441 *
        radiusPolynomialRoot16 (d.f0 12441 161) (d.f1 12441 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12441 : ℝ) ^ 8 * (mA 12441 : ℝ) ^ 8 *
        ((((4824966653 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4824966653 / 1000000000000000000)) * ((321938087 / 200000000000000000)) * (126 / 100) +
          2 * (((321938087 / 200000000000000000)) ^ 2 + 2 * ((4824966653 / 1000000000000000000)) * ((3095117 / 8000000000000000))) +
          6 * ((321938087 / 200000000000000000)) * ((3095117 / 8000000000000000)) * (126 / 100) + 8 * ((3095117 / 8000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12441) *
          (32 * (((4824966653 / 1000000000000000000) : ℝ) + (321938087 / 200000000000000000) + (3095117 / 8000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12441 : ℝ) ^ 16 *
      (d.w0 12441 161 + d.w1 12441 161 * √(π / 2) + 2 * d.w2 12441 161 +
        energyR16 12441 * radiusPolynomialRoot16 (d.w0 12441 161) (d.w1 12441 161)
          (d.w2 12441 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12441 : ℝ) ^ 16 *
        (((975049159 / 50000000000000000000) : ℝ) + ((138745761 / 10000000000000000000)) * (126 / 100) + 2 * ((506942593 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12441) *
          (32 * (((975049159 / 50000000000000000000) : ℝ) + (138745761 / 10000000000000000000) + (506942593 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12441

/-! A coarse bound on the actual paper statistics constant at dimension 12442. -/
namespace BstLean.Part266.Row12442
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12440 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12440 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12440 128 ≤ (12694 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12694 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12442) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12442 : ℕ))
    (by norm_num : (12442 : ℕ) ≤ 16384)
  have ht : paperTail256 12442 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12442 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12442 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12442 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12442 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12442 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12440 128 * √(2 / (12442 : ℝ)) *
      (√(12442 : ℝ) + paperT0 12442 + paperTail256 12442) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12442 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12442 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12442 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12440 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12440 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12442 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12442

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12442
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12442 (61 / 100) 161 (17 / (100 * 12442)) (26 / (10 * 12442)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12442 (61 / 100) 161 (17 / (100 * 12442)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (253407257 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1629366731 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6034647201 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12442 / 12442 * (61 / 100)) ^ 4 * inverseRadius8 (12442 - 1) /
            envelopeGap 12442 (61 / 100) 161 (17 / (100 * 12442)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12442

namespace BstLean.Part266.Row12442
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12442 161 ≤ (4823995067 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12442 161 ≤ (1609366511 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (96702957 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12442 161 ≤ (1949627691 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12442 161 ≤ (1387122867 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12442 161 ≤ (12670509 / 2500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (253407257 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (253407257 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1629366731 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6034647201 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3696403 / 1000000000) : ℝ) ≤ √(17 / (100 * 12442) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12442) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2251254127 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (10091353759 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12442) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12442) ≤ (113664489 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12442) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12442 * (161 : ℝ) ^ 2 + 26 / (10 * 12442) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12442) : ℝ)) (tA 12442 * 161 ^ 2 + 26 / (10 * 12442)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3696403 / 1000000000))) * ((253407257 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3696403 / 1000000000)) ^ 3) * ((1629366731 / 1000000000000000000000000))) + ((6034647201 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3696403 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12442) : ℝ)) d.D d.V d.P (√(tA 12442) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3696403 / 1000000000)) ^ 2 * (((2251254127 / 1000000000000000)) * ((10091353759 / 250000000000000000)))) + ((6034647201 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12442) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3696403 / 1000000000)) * ((253407257 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12442) : ℝ)) (tA 12442 * 161 ^ 2 + 26 / (10 * 12442)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((253407257 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3696403 / 1000000000)) ^ 2) * ((1629366731 / 1000000000000000000000000)) + ((6034647201 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12442) : ℝ)) (√(26 / (10 * 12442) : ℝ)) d.D d.V d.P (√(tA 12442) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3696403 / 1000000000)) * (((2251254127 / 1000000000000000)) * ((10091353759 / 250000000000000000))) + ((6034647201 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12442) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((253407257 / 50000000000000000000) : ℝ) + ((6034647201 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12442

namespace BstLean.Part266.Row12442
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12442 161 ∧
    0 ≤ (tableEnvelope C).f1 12442 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12442 161 ∧
    0 ≤ (tableEnvelope C).w1 12442 161 ∧ 0 ≤ (tableEnvelope C).w2 12442 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12442 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12442 161 ∧ 0 ≤ d.f1 12442 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12442 161 ∧ 0 ≤ d.w1 12442 161 ∧ 0 ≤ d.w2 12442 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12442 ≤ 2 * (228 / 100 : ℝ) / 12442 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12442 ≤ 2 * (370 / 100 : ℝ) / 12442 := by
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
    (completeRAData (tableEnvelope C) 12442 161).locationBound 12442 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12442 161).energyBound 12442 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12442 161) (d.f1 12442 161) d.f2 ≤
      32 * (((4823995067 / 1000000000000000000) : ℝ) + (1609366511 / 1000000000000000000) + (96702957 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12442 161) (d.w1 12442 161)
      (d.w2 12442 161) ≤
      32 * (((1949627691 / 100000000000000000000) : ℝ) + (1387122867 / 100000000000000000000) + (12670509 / 2500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12442 161) (d.f1 12442 161) d.f2 ≤
      ((4823995067 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4823995067 / 1000000000000000000)) * ((1609366511 / 1000000000000000000)) * (126 / 100) +
      2 * (((1609366511 / 1000000000000000000)) ^ 2 + 2 * ((4823995067 / 1000000000000000000)) * ((96702957 / 250000000000000000))) +
      6 * ((1609366511 / 1000000000000000000)) * ((96702957 / 250000000000000000)) * (126 / 100) + 8 * ((96702957 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12442 161) (d.f1 12442 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12442 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12442 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12442 161) (d.f1 12442 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12442 161) (d.w1 12442 161) (d.w2 12442 161)
  have hwexpr0 : 0 ≤ d.w0 12442 161 + d.w1 12442 161 * √(π / 2) +
      2 * d.w2 12442 161 + energyR16 12442 *
      radiusPolynomialRoot16 (d.w0 12442 161) (d.w1 12442 161) (d.w2 12442 161) := by
    positivity
  constructor
  · change (12442 : ℝ) ^ 8 * (mA 12442 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12442 161) (d.f1 12442 161) d.f2 + locationR16 12442 *
        radiusPolynomialRoot16 (d.f0 12442 161) (d.f1 12442 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12442 : ℝ) ^ 8 * (mA 12442 : ℝ) ^ 8 *
        ((((4823995067 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4823995067 / 1000000000000000000)) * ((1609366511 / 1000000000000000000)) * (126 / 100) +
          2 * (((1609366511 / 1000000000000000000)) ^ 2 + 2 * ((4823995067 / 1000000000000000000)) * ((96702957 / 250000000000000000))) +
          6 * ((1609366511 / 1000000000000000000)) * ((96702957 / 250000000000000000)) * (126 / 100) + 8 * ((96702957 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12442) *
          (32 * (((4823995067 / 1000000000000000000) : ℝ) + (1609366511 / 1000000000000000000) + (96702957 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12442 : ℝ) ^ 16 *
      (d.w0 12442 161 + d.w1 12442 161 * √(π / 2) + 2 * d.w2 12442 161 +
        energyR16 12442 * radiusPolynomialRoot16 (d.w0 12442 161) (d.w1 12442 161)
          (d.w2 12442 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12442 : ℝ) ^ 16 *
        (((1949627691 / 100000000000000000000) : ℝ) + ((1387122867 / 100000000000000000000)) * (126 / 100) + 2 * ((12670509 / 2500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12442) *
          (32 * (((1949627691 / 100000000000000000000) : ℝ) + (1387122867 / 100000000000000000000) + (12670509 / 2500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12442

/-! A coarse bound on the actual paper statistics constant at dimension 12443. -/
namespace BstLean.Part266.Row12443
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12441 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12441 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12441 128 ≤ (12695 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12695 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12443) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12443 : ℕ))
    (by norm_num : (12443 : ℕ) ≤ 16384)
  have ht : paperTail256 12443 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12443 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12443 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12443 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12443 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12443 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12441 128 * √(2 / (12443 : ℝ)) *
      (√(12443 : ℝ) + paperT0 12443 + paperTail256 12443) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12443 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12443 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12443 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12441 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12441 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12443 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12443

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12443
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12443 (61 / 100) 161 (17 / (100 * 12443)) (26 / (10 * 12443)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12443 (61 / 100) 161 (17 / (100 * 12443)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (20267693 / 4000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (407210747 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6030730029 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12443 / 12443 * (61 / 100)) ^ 4 * inverseRadius8 (12443 - 1) /
            envelopeGap 12443 (61 / 100) 161 (17 / (100 * 12443)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12443

namespace BstLean.Part266.Row12443
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12443 161 ≤ (602878449 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12443 161 ≤ (804521783 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (386734159 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12443 161 ≤ (487289503 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12443 161 ≤ (173348577 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 12443 161 ≤ (506698167 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (20267693 / 4000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (20267693 / 4000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (407210747 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6030730029 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1848127 / 500000000) : ℝ) ≤ √(17 / (100 * 12443) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12443) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (225098273 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40358926993 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12443) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12443) ≤ (56827677 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12443) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12443 * (161 : ℝ) ^ 2 + 26 / (10 * 12443) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12443) : ℝ)) (tA 12443 * 161 ^ 2 + 26 / (10 * 12443)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1848127 / 500000000))) * ((20267693 / 4000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1848127 / 500000000)) ^ 3) * ((407210747 / 250000000000000000000000))) + ((6030730029 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1848127 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12443) : ℝ)) d.D d.V d.P (√(tA 12443) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1848127 / 500000000)) ^ 2 * (((225098273 / 100000000000000)) * ((40358926993 / 1000000000000000000)))) + ((6030730029 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12443) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1848127 / 500000000)) * ((20267693 / 4000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12443) : ℝ)) (tA 12443 * 161 ^ 2 + 26 / (10 * 12443)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((20267693 / 4000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1848127 / 500000000)) ^ 2) * ((407210747 / 250000000000000000000000)) + ((6030730029 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12443) : ℝ)) (√(26 / (10 * 12443) : ℝ)) d.D d.V d.P (√(tA 12443) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1848127 / 500000000)) * (((225098273 / 100000000000000)) * ((40358926993 / 1000000000000000000))) + ((6030730029 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12443) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((20267693 / 4000000000000000000) : ℝ) + ((6030730029 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12443

namespace BstLean.Part266.Row12443
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12443 161 ∧
    0 ≤ (tableEnvelope C).f1 12443 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12443 161 ∧
    0 ≤ (tableEnvelope C).w1 12443 161 ∧ 0 ≤ (tableEnvelope C).w2 12443 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12443 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12443 161 ∧ 0 ≤ d.f1 12443 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12443 161 ∧ 0 ≤ d.w1 12443 161 ∧ 0 ≤ d.w2 12443 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12443 ≤ 2 * (228 / 100 : ℝ) / 12443 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12443 ≤ 2 * (370 / 100 : ℝ) / 12443 := by
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
    (completeRAData (tableEnvelope C) 12443 161).locationBound 12443 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12443 161).energyBound 12443 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12443 161) (d.f1 12443 161) d.f2 ≤
      32 * (((602878449 / 125000000000000000) : ℝ) + (804521783 / 500000000000000000) + (386734159 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12443 161) (d.w1 12443 161)
      (d.w2 12443 161) ≤
      32 * (((487289503 / 25000000000000000000) : ℝ) + (173348577 / 12500000000000000000) + (506698167 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12443 161) (d.f1 12443 161) d.f2 ≤
      ((602878449 / 125000000000000000) : ℝ) ^ 2 + 2 * ((602878449 / 125000000000000000)) * ((804521783 / 500000000000000000)) * (126 / 100) +
      2 * (((804521783 / 500000000000000000)) ^ 2 + 2 * ((602878449 / 125000000000000000)) * ((386734159 / 1000000000000000000))) +
      6 * ((804521783 / 500000000000000000)) * ((386734159 / 1000000000000000000)) * (126 / 100) + 8 * ((386734159 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12443 161) (d.f1 12443 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12443 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12443 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12443 161) (d.f1 12443 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12443 161) (d.w1 12443 161) (d.w2 12443 161)
  have hwexpr0 : 0 ≤ d.w0 12443 161 + d.w1 12443 161 * √(π / 2) +
      2 * d.w2 12443 161 + energyR16 12443 *
      radiusPolynomialRoot16 (d.w0 12443 161) (d.w1 12443 161) (d.w2 12443 161) := by
    positivity
  constructor
  · change (12443 : ℝ) ^ 8 * (mA 12443 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12443 161) (d.f1 12443 161) d.f2 + locationR16 12443 *
        radiusPolynomialRoot16 (d.f0 12443 161) (d.f1 12443 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12443 : ℝ) ^ 8 * (mA 12443 : ℝ) ^ 8 *
        ((((602878449 / 125000000000000000) : ℝ) ^ 2 + 2 * ((602878449 / 125000000000000000)) * ((804521783 / 500000000000000000)) * (126 / 100) +
          2 * (((804521783 / 500000000000000000)) ^ 2 + 2 * ((602878449 / 125000000000000000)) * ((386734159 / 1000000000000000000))) +
          6 * ((804521783 / 500000000000000000)) * ((386734159 / 1000000000000000000)) * (126 / 100) + 8 * ((386734159 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12443) *
          (32 * (((602878449 / 125000000000000000) : ℝ) + (804521783 / 500000000000000000) + (386734159 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12443 : ℝ) ^ 16 *
      (d.w0 12443 161 + d.w1 12443 161 * √(π / 2) + 2 * d.w2 12443 161 +
        energyR16 12443 * radiusPolynomialRoot16 (d.w0 12443 161) (d.w1 12443 161)
          (d.w2 12443 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12443 : ℝ) ^ 16 *
        (((487289503 / 25000000000000000000) : ℝ) + ((173348577 / 12500000000000000000)) * (126 / 100) + 2 * ((506698167 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12443) *
          (32 * (((487289503 / 25000000000000000000) : ℝ) + (173348577 / 12500000000000000000) + (506698167 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12443

/-! A coarse bound on the actual paper statistics constant at dimension 12444. -/
namespace BstLean.Part266.Row12444
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12442 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12442 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12442 128 ≤ (12696 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12696 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12444) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12444 : ℕ))
    (by norm_num : (12444 : ℕ) ≤ 16384)
  have ht : paperTail256 12444 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12444 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12444 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12444 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12444 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12444 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12442 128 * √(2 / (12444 : ℝ)) *
      (√(12444 : ℝ) + paperT0 12444 + paperTail256 12444) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12444 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12444 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12444 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12442 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12442 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12444 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12444

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12444
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12444 (61 / 100) 161 (17 / (100 * 12444)) (26 / (10 * 12444)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12444 (61 / 100) 161 (17 / (100 * 12444)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (20262807 / 4000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (814159727 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (150670393 / 25000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12444 / 12444 * (61 / 100)) ^ 4 * inverseRadius8 (12444 - 1) /
            envelopeGap 12444 (61 / 100) 161 (17 / (100 * 12444)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12444

namespace BstLean.Part266.Row12444
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12444 161 ≤ (4822056687 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12444 161 ≤ (100544991 / 62500000000000000)
  f2 : (tableEnvelope C).f2 ≤ (38665641 / 100000000000000000)
  w0 : (tableEnvelope C).w0 12444 161 ≤ (487171929 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12444 161 ≤ (1386454103 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12444 161 ≤ (253288007 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (20262807 / 4000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (20262807 / 4000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (814159727 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (150670393 / 25000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1848053 / 500000000) : ℝ) ≤ √(17 / (100 * 12444) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12444) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (562677847 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40352440497 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12444) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12444) ≤ (113646221 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12444) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12444 * (161 : ℝ) ^ 2 + 26 / (10 * 12444) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12444) : ℝ)) (tA 12444 * 161 ^ 2 + 26 / (10 * 12444)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1848053 / 500000000))) * ((20262807 / 4000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1848053 / 500000000)) ^ 3) * ((814159727 / 500000000000000000000000))) + ((150670393 / 25000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1848053 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12444) : ℝ)) d.D d.V d.P (√(tA 12444) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1848053 / 500000000)) ^ 2 * (((562677847 / 250000000000000)) * ((40352440497 / 1000000000000000000)))) + ((150670393 / 25000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12444) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1848053 / 500000000)) * ((20262807 / 4000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12444) : ℝ)) (tA 12444 * 161 ^ 2 + 26 / (10 * 12444)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((20262807 / 4000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1848053 / 500000000)) ^ 2) * ((814159727 / 500000000000000000000000)) + ((150670393 / 25000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12444) : ℝ)) (√(26 / (10 * 12444) : ℝ)) d.D d.V d.P (√(tA 12444) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1848053 / 500000000)) * (((562677847 / 250000000000000)) * ((40352440497 / 1000000000000000000))) + ((150670393 / 25000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12444) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((20262807 / 4000000000000000000) : ℝ) + ((150670393 / 25000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12444

namespace BstLean.Part266.Row12444
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12444 161 ∧
    0 ≤ (tableEnvelope C).f1 12444 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12444 161 ∧
    0 ≤ (tableEnvelope C).w1 12444 161 ∧ 0 ≤ (tableEnvelope C).w2 12444 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12444 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12444 161 ∧ 0 ≤ d.f1 12444 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12444 161 ∧ 0 ≤ d.w1 12444 161 ∧ 0 ≤ d.w2 12444 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12444 ≤ 2 * (228 / 100 : ℝ) / 12444 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12444 ≤ 2 * (370 / 100 : ℝ) / 12444 := by
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
    (completeRAData (tableEnvelope C) 12444 161).locationBound 12444 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12444 161).energyBound 12444 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12444 161) (d.f1 12444 161) d.f2 ≤
      32 * (((4822056687 / 1000000000000000000) : ℝ) + (100544991 / 62500000000000000) + (38665641 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12444 161) (d.w1 12444 161)
      (d.w2 12444 161) ≤
      32 * (((487171929 / 25000000000000000000) : ℝ) + (1386454103 / 100000000000000000000) + (253288007 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12444 161) (d.f1 12444 161) d.f2 ≤
      ((4822056687 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4822056687 / 1000000000000000000)) * ((100544991 / 62500000000000000)) * (126 / 100) +
      2 * (((100544991 / 62500000000000000)) ^ 2 + 2 * ((4822056687 / 1000000000000000000)) * ((38665641 / 100000000000000000))) +
      6 * ((100544991 / 62500000000000000)) * ((38665641 / 100000000000000000)) * (126 / 100) + 8 * ((38665641 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12444 161) (d.f1 12444 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12444 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12444 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12444 161) (d.f1 12444 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12444 161) (d.w1 12444 161) (d.w2 12444 161)
  have hwexpr0 : 0 ≤ d.w0 12444 161 + d.w1 12444 161 * √(π / 2) +
      2 * d.w2 12444 161 + energyR16 12444 *
      radiusPolynomialRoot16 (d.w0 12444 161) (d.w1 12444 161) (d.w2 12444 161) := by
    positivity
  constructor
  · change (12444 : ℝ) ^ 8 * (mA 12444 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12444 161) (d.f1 12444 161) d.f2 + locationR16 12444 *
        radiusPolynomialRoot16 (d.f0 12444 161) (d.f1 12444 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12444 : ℝ) ^ 8 * (mA 12444 : ℝ) ^ 8 *
        ((((4822056687 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4822056687 / 1000000000000000000)) * ((100544991 / 62500000000000000)) * (126 / 100) +
          2 * (((100544991 / 62500000000000000)) ^ 2 + 2 * ((4822056687 / 1000000000000000000)) * ((38665641 / 100000000000000000))) +
          6 * ((100544991 / 62500000000000000)) * ((38665641 / 100000000000000000)) * (126 / 100) + 8 * ((38665641 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12444) *
          (32 * (((4822056687 / 1000000000000000000) : ℝ) + (100544991 / 62500000000000000) + (38665641 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12444 : ℝ) ^ 16 *
      (d.w0 12444 161 + d.w1 12444 161 * √(π / 2) + 2 * d.w2 12444 161 +
        energyR16 12444 * radiusPolynomialRoot16 (d.w0 12444 161) (d.w1 12444 161)
          (d.w2 12444 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12444 : ℝ) ^ 16 *
        (((487171929 / 25000000000000000000) : ℝ) + ((1386454103 / 100000000000000000000)) * (126 / 100) + 2 * ((253288007 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12444) *
          (32 * (((487171929 / 25000000000000000000) : ℝ) + (1386454103 / 100000000000000000000) + (253288007 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12444

/-! A coarse bound on the actual paper statistics constant at dimension 12445. -/
namespace BstLean.Part266.Row12445
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12443 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12443 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12443 128 ≤ (12697 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12697 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12445) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12445 : ℕ))
    (by norm_num : (12445 : ℕ) ≤ 16384)
  have ht : paperTail256 12445 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12445 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12445 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12445 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12445 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12445 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12443 128 * √(2 / (12445 : ℝ)) *
      (√(12445 : ℝ) + paperT0 12445 + paperTail256 12445) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12445 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12445 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12445 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12443 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12443 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12445 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12445

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12445
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12445 (61 / 100) 161 (17 / (100 * 12445)) (26 / (10 * 12445)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12445 (61 / 100) 161 (17 / (100 * 12445)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (7913251 / 1562500000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1627796131 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (376431517 / 62500000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12445 / 12445 * (61 / 100)) ^ 4 * inverseRadius8 (12445 - 1) /
            envelopeGap 12445 (61 / 100) 161 (17 / (100 * 12445)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12445

namespace BstLean.Part266.Row12445
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12445 161 ≤ (482108989 / 100000000000000000)
  f1 : (tableEnvelope C).f1 12445 161 ≤ (1608397123 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (386578789 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12445 161 ≤ (974109183 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12445 161 ≤ (1386120079 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12445 161 ≤ (506453899 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (7913251 / 1562500000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (7913251 / 1562500000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1627796131 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (376431517 / 62500000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3695957 / 1000000000) : ℝ) ≤ √(17 / (100 * 12445) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12445) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (22504401 / 10000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (10086488893 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12445) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12445) ≤ (113637089 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12445) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12445 * (161 : ℝ) ^ 2 + 26 / (10 * 12445) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12445) : ℝ)) (tA 12445 * 161 ^ 2 + 26 / (10 * 12445)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3695957 / 1000000000))) * ((7913251 / 1562500000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3695957 / 1000000000)) ^ 3) * ((1627796131 / 1000000000000000000000000))) + ((376431517 / 62500000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3695957 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12445) : ℝ)) d.D d.V d.P (√(tA 12445) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3695957 / 1000000000)) ^ 2 * (((22504401 / 10000000000000)) * ((10086488893 / 250000000000000000)))) + ((376431517 / 62500000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12445) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3695957 / 1000000000)) * ((7913251 / 1562500000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12445) : ℝ)) (tA 12445 * 161 ^ 2 + 26 / (10 * 12445)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((7913251 / 1562500000000000000) : ℝ) + (24198 / 100000) / (2 * ((3695957 / 1000000000)) ^ 2) * ((1627796131 / 1000000000000000000000000)) + ((376431517 / 62500000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12445) : ℝ)) (√(26 / (10 * 12445) : ℝ)) d.D d.V d.P (√(tA 12445) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3695957 / 1000000000)) * (((22504401 / 10000000000000)) * ((10086488893 / 250000000000000000))) + ((376431517 / 62500000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12445) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((7913251 / 1562500000000000000) : ℝ) + ((376431517 / 62500000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12445

namespace BstLean.Part266.Row12445
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12445 161 ∧
    0 ≤ (tableEnvelope C).f1 12445 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12445 161 ∧
    0 ≤ (tableEnvelope C).w1 12445 161 ∧ 0 ≤ (tableEnvelope C).w2 12445 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12445 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12445 161 ∧ 0 ≤ d.f1 12445 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12445 161 ∧ 0 ≤ d.w1 12445 161 ∧ 0 ≤ d.w2 12445 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12445 ≤ 2 * (228 / 100 : ℝ) / 12445 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12445 ≤ 2 * (370 / 100 : ℝ) / 12445 := by
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
    (completeRAData (tableEnvelope C) 12445 161).locationBound 12445 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12445 161).energyBound 12445 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12445 161) (d.f1 12445 161) d.f2 ≤
      32 * (((482108989 / 100000000000000000) : ℝ) + (1608397123 / 1000000000000000000) + (386578789 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12445 161) (d.w1 12445 161)
      (d.w2 12445 161) ≤
      32 * (((974109183 / 50000000000000000000) : ℝ) + (1386120079 / 100000000000000000000) + (506453899 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12445 161) (d.f1 12445 161) d.f2 ≤
      ((482108989 / 100000000000000000) : ℝ) ^ 2 + 2 * ((482108989 / 100000000000000000)) * ((1608397123 / 1000000000000000000)) * (126 / 100) +
      2 * (((1608397123 / 1000000000000000000)) ^ 2 + 2 * ((482108989 / 100000000000000000)) * ((386578789 / 1000000000000000000))) +
      6 * ((1608397123 / 1000000000000000000)) * ((386578789 / 1000000000000000000)) * (126 / 100) + 8 * ((386578789 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12445 161) (d.f1 12445 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12445 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12445 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12445 161) (d.f1 12445 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12445 161) (d.w1 12445 161) (d.w2 12445 161)
  have hwexpr0 : 0 ≤ d.w0 12445 161 + d.w1 12445 161 * √(π / 2) +
      2 * d.w2 12445 161 + energyR16 12445 *
      radiusPolynomialRoot16 (d.w0 12445 161) (d.w1 12445 161) (d.w2 12445 161) := by
    positivity
  constructor
  · change (12445 : ℝ) ^ 8 * (mA 12445 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12445 161) (d.f1 12445 161) d.f2 + locationR16 12445 *
        radiusPolynomialRoot16 (d.f0 12445 161) (d.f1 12445 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12445 : ℝ) ^ 8 * (mA 12445 : ℝ) ^ 8 *
        ((((482108989 / 100000000000000000) : ℝ) ^ 2 + 2 * ((482108989 / 100000000000000000)) * ((1608397123 / 1000000000000000000)) * (126 / 100) +
          2 * (((1608397123 / 1000000000000000000)) ^ 2 + 2 * ((482108989 / 100000000000000000)) * ((386578789 / 1000000000000000000))) +
          6 * ((1608397123 / 1000000000000000000)) * ((386578789 / 1000000000000000000)) * (126 / 100) + 8 * ((386578789 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12445) *
          (32 * (((482108989 / 100000000000000000) : ℝ) + (1608397123 / 1000000000000000000) + (386578789 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12445 : ℝ) ^ 16 *
      (d.w0 12445 161 + d.w1 12445 161 * √(π / 2) + 2 * d.w2 12445 161 +
        energyR16 12445 * radiusPolynomialRoot16 (d.w0 12445 161) (d.w1 12445 161)
          (d.w2 12445 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12445 : ℝ) ^ 16 *
        (((974109183 / 50000000000000000000) : ℝ) + ((1386120079 / 100000000000000000000)) * (126 / 100) + 2 * ((506453899 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12445) *
          (32 * (((974109183 / 50000000000000000000) : ℝ) + (1386120079 / 100000000000000000000) + (506453899 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12445

/-! A coarse bound on the actual paper statistics constant at dimension 12446. -/
namespace BstLean.Part266.Row12446
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12444 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12444 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12444 128 ≤ (12698 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12698 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12446) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12446 : ℕ))
    (by norm_num : (12446 : ℕ) ≤ 16384)
  have ht : paperTail256 12446 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12446 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12446 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12446 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12446 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12446 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12444 128 * √(2 / (12446 : ℝ)) *
      (√(12446 : ℝ) + paperT0 12446 + paperTail256 12446) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12446 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12446 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12446 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12444 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12444 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12446 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12446

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12446
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12446 (61 / 100) 161 (17 / (100 * 12446)) (26 / (10 * 12446)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12446 (61 / 100) 161 (17 / (100 * 12446)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (63290749 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1627273019 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3009497841 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12446 / 12446 * (61 / 100)) ^ 4 * inverseRadius8 (12446 - 1) /
            envelopeGap 12446 (61 / 100) 161 (17 / (100 * 12446)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12446

namespace BstLean.Part266.Row12446
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12446 161 ≤ (4820119669 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12446 161 ≤ (804036813 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (386501087 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12446 161 ≤ (4869371 / 250000000000000000)
  w1 : (tableEnvelope C).w1 12446 161 ≤ (692892897 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12446 161 ≤ (506331823 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (63290749 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (63290749 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1627273019 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3009497841 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3695809 / 1000000000) : ℝ) ≤ √(17 / (100 * 12446) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12446) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (450033773 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40339472221 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12446) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12446) ≤ (56813979 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12446) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12446 * (161 : ℝ) ^ 2 + 26 / (10 * 12446) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12446) : ℝ)) (tA 12446 * 161 ^ 2 + 26 / (10 * 12446)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3695809 / 1000000000))) * ((63290749 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3695809 / 1000000000)) ^ 3) * ((1627273019 / 1000000000000000000000000))) + ((3009497841 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3695809 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12446) : ℝ)) d.D d.V d.P (√(tA 12446) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3695809 / 1000000000)) ^ 2 * (((450033773 / 200000000000000)) * ((40339472221 / 1000000000000000000)))) + ((3009497841 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12446) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3695809 / 1000000000)) * ((63290749 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12446) : ℝ)) (tA 12446 * 161 ^ 2 + 26 / (10 * 12446)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((63290749 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3695809 / 1000000000)) ^ 2) * ((1627273019 / 1000000000000000000000000)) + ((3009497841 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12446) : ℝ)) (√(26 / (10 * 12446) : ℝ)) d.D d.V d.P (√(tA 12446) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3695809 / 1000000000)) * (((450033773 / 200000000000000)) * ((40339472221 / 1000000000000000000))) + ((3009497841 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12446) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((63290749 / 12500000000000000000) : ℝ) + ((3009497841 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12446

namespace BstLean.Part266.Row12446
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12446 161 ∧
    0 ≤ (tableEnvelope C).f1 12446 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12446 161 ∧
    0 ≤ (tableEnvelope C).w1 12446 161 ∧ 0 ≤ (tableEnvelope C).w2 12446 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12446 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12446 161 ∧ 0 ≤ d.f1 12446 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12446 161 ∧ 0 ≤ d.w1 12446 161 ∧ 0 ≤ d.w2 12446 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12446 ≤ 2 * (228 / 100 : ℝ) / 12446 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12446 ≤ 2 * (370 / 100 : ℝ) / 12446 := by
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
    (completeRAData (tableEnvelope C) 12446 161).locationBound 12446 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12446 161).energyBound 12446 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12446 161) (d.f1 12446 161) d.f2 ≤
      32 * (((4820119669 / 1000000000000000000) : ℝ) + (804036813 / 500000000000000000) + (386501087 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12446 161) (d.w1 12446 161)
      (d.w2 12446 161) ≤
      32 * (((4869371 / 250000000000000000) : ℝ) + (692892897 / 50000000000000000000) + (506331823 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12446 161) (d.f1 12446 161) d.f2 ≤
      ((4820119669 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4820119669 / 1000000000000000000)) * ((804036813 / 500000000000000000)) * (126 / 100) +
      2 * (((804036813 / 500000000000000000)) ^ 2 + 2 * ((4820119669 / 1000000000000000000)) * ((386501087 / 1000000000000000000))) +
      6 * ((804036813 / 500000000000000000)) * ((386501087 / 1000000000000000000)) * (126 / 100) + 8 * ((386501087 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12446 161) (d.f1 12446 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12446 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12446 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12446 161) (d.f1 12446 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12446 161) (d.w1 12446 161) (d.w2 12446 161)
  have hwexpr0 : 0 ≤ d.w0 12446 161 + d.w1 12446 161 * √(π / 2) +
      2 * d.w2 12446 161 + energyR16 12446 *
      radiusPolynomialRoot16 (d.w0 12446 161) (d.w1 12446 161) (d.w2 12446 161) := by
    positivity
  constructor
  · change (12446 : ℝ) ^ 8 * (mA 12446 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12446 161) (d.f1 12446 161) d.f2 + locationR16 12446 *
        radiusPolynomialRoot16 (d.f0 12446 161) (d.f1 12446 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12446 : ℝ) ^ 8 * (mA 12446 : ℝ) ^ 8 *
        ((((4820119669 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4820119669 / 1000000000000000000)) * ((804036813 / 500000000000000000)) * (126 / 100) +
          2 * (((804036813 / 500000000000000000)) ^ 2 + 2 * ((4820119669 / 1000000000000000000)) * ((386501087 / 1000000000000000000))) +
          6 * ((804036813 / 500000000000000000)) * ((386501087 / 1000000000000000000)) * (126 / 100) + 8 * ((386501087 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12446) *
          (32 * (((4820119669 / 1000000000000000000) : ℝ) + (804036813 / 500000000000000000) + (386501087 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12446 : ℝ) ^ 16 *
      (d.w0 12446 161 + d.w1 12446 161 * √(π / 2) + 2 * d.w2 12446 161 +
        energyR16 12446 * radiusPolynomialRoot16 (d.w0 12446 161) (d.w1 12446 161)
          (d.w2 12446 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12446 : ℝ) ^ 16 *
        (((4869371 / 250000000000000000) : ℝ) + ((692892897 / 50000000000000000000)) * (126 / 100) + 2 * ((506331823 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12446) *
          (32 * (((4869371 / 250000000000000000) : ℝ) + (692892897 / 50000000000000000000) + (506331823 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12446

/-! A coarse bound on the actual paper statistics constant at dimension 12447. -/
namespace BstLean.Part266.Row12447
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12445 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12445 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12445 128 ≤ (12699 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12699 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12447) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12447 : ℕ))
    (by norm_num : (12447 : ℕ) ≤ 16384)
  have ht : paperTail256 12447 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12447 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12447 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12447 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12447 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12447 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12445 128 * √(2 / (12447 : ℝ)) *
      (√(12447 : ℝ) + paperT0 12447 + paperTail256 12447) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12447 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12447 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12447 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12445 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12445 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12447 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12447

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12447
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12447 (61 / 100) 161 (17 / (100 * 12447)) (26 / (10 * 12447)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12447 (61 / 100) 161 (17 / (100 * 12447)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (12655099 / 2500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (406687529 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6015089949 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12447 / 12447 * (61 / 100)) ^ 4 * inverseRadius8 (12447 - 1) /
            envelopeGap 12447 (61 / 100) 161 (17 / (100 * 12447)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12447

namespace BstLean.Part266.Row12447
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12447 161 ≤ (96383071 / 20000000000000000)
  f1 : (tableEnvelope C).f1 12447 161 ≤ (1607751107 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (386423513 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12447 161 ≤ (97363969 / 5000000000000000000)
  w1 : (tableEnvelope C).w1 12447 161 ≤ (1385451999 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12447 161 ≤ (506209787 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (12655099 / 2500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (12655099 / 2500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (406687529 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6015089949 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((184783 / 50000000) : ℝ) ≤ √(17 / (100 * 12447) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12447) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2249897687 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (20166495209 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12447) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12447) ≤ (113618829 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12447) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12447 * (161 : ℝ) ^ 2 + 26 / (10 * 12447) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12447) : ℝ)) (tA 12447 * 161 ^ 2 + 26 / (10 * 12447)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((184783 / 50000000))) * ((12655099 / 2500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((184783 / 50000000)) ^ 3) * ((406687529 / 250000000000000000000000))) + ((6015089949 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((184783 / 50000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12447) : ℝ)) d.D d.V d.P (√(tA 12447) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((184783 / 50000000)) ^ 2 * (((2249897687 / 1000000000000000)) * ((20166495209 / 500000000000000000)))) + ((6015089949 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12447) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((184783 / 50000000)) * ((12655099 / 2500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12447) : ℝ)) (tA 12447 * 161 ^ 2 + 26 / (10 * 12447)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((12655099 / 2500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((184783 / 50000000)) ^ 2) * ((406687529 / 250000000000000000000000)) + ((6015089949 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12447) : ℝ)) (√(26 / (10 * 12447) : ℝ)) d.D d.V d.P (√(tA 12447) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((184783 / 50000000)) * (((2249897687 / 1000000000000000)) * ((20166495209 / 500000000000000000))) + ((6015089949 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12447) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((12655099 / 2500000000000000000) : ℝ) + ((6015089949 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12447

namespace BstLean.Part266.Row12447
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12447 161 ∧
    0 ≤ (tableEnvelope C).f1 12447 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12447 161 ∧
    0 ≤ (tableEnvelope C).w1 12447 161 ∧ 0 ≤ (tableEnvelope C).w2 12447 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12447 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12447 161 ∧ 0 ≤ d.f1 12447 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12447 161 ∧ 0 ≤ d.w1 12447 161 ∧ 0 ≤ d.w2 12447 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12447 ≤ 2 * (228 / 100 : ℝ) / 12447 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12447 ≤ 2 * (370 / 100 : ℝ) / 12447 := by
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
    (completeRAData (tableEnvelope C) 12447 161).locationBound 12447 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12447 161).energyBound 12447 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12447 161) (d.f1 12447 161) d.f2 ≤
      32 * (((96383071 / 20000000000000000) : ℝ) + (1607751107 / 1000000000000000000) + (386423513 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12447 161) (d.w1 12447 161)
      (d.w2 12447 161) ≤
      32 * (((97363969 / 5000000000000000000) : ℝ) + (1385451999 / 100000000000000000000) + (506209787 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12447 161) (d.f1 12447 161) d.f2 ≤
      ((96383071 / 20000000000000000) : ℝ) ^ 2 + 2 * ((96383071 / 20000000000000000)) * ((1607751107 / 1000000000000000000)) * (126 / 100) +
      2 * (((1607751107 / 1000000000000000000)) ^ 2 + 2 * ((96383071 / 20000000000000000)) * ((386423513 / 1000000000000000000))) +
      6 * ((1607751107 / 1000000000000000000)) * ((386423513 / 1000000000000000000)) * (126 / 100) + 8 * ((386423513 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12447 161) (d.f1 12447 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12447 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12447 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12447 161) (d.f1 12447 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12447 161) (d.w1 12447 161) (d.w2 12447 161)
  have hwexpr0 : 0 ≤ d.w0 12447 161 + d.w1 12447 161 * √(π / 2) +
      2 * d.w2 12447 161 + energyR16 12447 *
      radiusPolynomialRoot16 (d.w0 12447 161) (d.w1 12447 161) (d.w2 12447 161) := by
    positivity
  constructor
  · change (12447 : ℝ) ^ 8 * (mA 12447 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12447 161) (d.f1 12447 161) d.f2 + locationR16 12447 *
        radiusPolynomialRoot16 (d.f0 12447 161) (d.f1 12447 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12447 : ℝ) ^ 8 * (mA 12447 : ℝ) ^ 8 *
        ((((96383071 / 20000000000000000) : ℝ) ^ 2 + 2 * ((96383071 / 20000000000000000)) * ((1607751107 / 1000000000000000000)) * (126 / 100) +
          2 * (((1607751107 / 1000000000000000000)) ^ 2 + 2 * ((96383071 / 20000000000000000)) * ((386423513 / 1000000000000000000))) +
          6 * ((1607751107 / 1000000000000000000)) * ((386423513 / 1000000000000000000)) * (126 / 100) + 8 * ((386423513 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12447) *
          (32 * (((96383071 / 20000000000000000) : ℝ) + (1607751107 / 1000000000000000000) + (386423513 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12447 : ℝ) ^ 16 *
      (d.w0 12447 161 + d.w1 12447 161 * √(π / 2) + 2 * d.w2 12447 161 +
        energyR16 12447 * radiusPolynomialRoot16 (d.w0 12447 161) (d.w1 12447 161)
          (d.w2 12447 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12447 : ℝ) ^ 16 *
        (((97363969 / 5000000000000000000) : ℝ) + ((1385451999 / 100000000000000000000)) * (126 / 100) + 2 * ((506209787 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12447) *
          (32 * (((97363969 / 5000000000000000000) : ℝ) + (1385451999 / 100000000000000000000) + (506209787 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12447

/-! A coarse bound on the actual paper statistics constant at dimension 12448. -/
namespace BstLean.Part266.Row12448
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12446 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12446 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12446 128 ≤ (12700 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12700 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12448) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12448 : ℕ))
    (by norm_num : (12448 : ℕ) ≤ 16384)
  have ht : paperTail256 12448 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12448 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12448 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12448 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12448 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12448 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12446 128 * √(2 / (12448 : ℝ)) *
      (√(12448 : ℝ) + paperT0 12448 + paperTail256 12448) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12448 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12448 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12448 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12446 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12446 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12448 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12448

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12448
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12448 (61 / 100) 161 (17 / (100 * 12448)) (26 / (10 * 12448)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12448 (61 / 100) 161 (17 / (100 * 12448)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (506081967 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1626227423 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (601118707 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12448 / 12448 * (61 / 100)) ^ 4 * inverseRadius8 (12448 - 1) /
            envelopeGap 12448 (61 / 100) 161 (17 / (100 * 12448)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12448

namespace BstLean.Part266.Row12448
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12448 161 ≤ (2409092003 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12448 161 ≤ (1607427823 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (386345859 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12448 161 ≤ (121675609 / 6250000000000000000)
  w1 : (tableEnvelope C).w1 12448 161 ≤ (1385117943 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12448 161 ≤ (50608779 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (506081967 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (506081967 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1626227423 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (601118707 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((461939 / 125000000) : ℝ) ≤ √(17 / (100 * 12448) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12448) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2249626563 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40326510177 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12448) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12448) ≤ (56804851 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12448) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12448 * (161 : ℝ) ^ 2 + 26 / (10 * 12448) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12448) : ℝ)) (tA 12448 * 161 ^ 2 + 26 / (10 * 12448)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((461939 / 125000000))) * ((506081967 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((461939 / 125000000)) ^ 3) * ((1626227423 / 1000000000000000000000000))) + ((601118707 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((461939 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12448) : ℝ)) d.D d.V d.P (√(tA 12448) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((461939 / 125000000)) ^ 2 * (((2249626563 / 1000000000000000)) * ((40326510177 / 1000000000000000000)))) + ((601118707 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12448) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((461939 / 125000000)) * ((506081967 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12448) : ℝ)) (tA 12448 * 161 ^ 2 + 26 / (10 * 12448)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((506081967 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((461939 / 125000000)) ^ 2) * ((1626227423 / 1000000000000000000000000)) + ((601118707 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12448) : ℝ)) (√(26 / (10 * 12448) : ℝ)) d.D d.V d.P (√(tA 12448) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((461939 / 125000000)) * (((2249626563 / 1000000000000000)) * ((40326510177 / 1000000000000000000))) + ((601118707 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12448) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((506081967 / 100000000000000000000) : ℝ) + ((601118707 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12448

namespace BstLean.Part266.Row12448
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12448 161 ∧
    0 ≤ (tableEnvelope C).f1 12448 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12448 161 ∧
    0 ≤ (tableEnvelope C).w1 12448 161 ∧ 0 ≤ (tableEnvelope C).w2 12448 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12448 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12448 161 ∧ 0 ≤ d.f1 12448 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12448 161 ∧ 0 ≤ d.w1 12448 161 ∧ 0 ≤ d.w2 12448 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12448 ≤ 2 * (228 / 100 : ℝ) / 12448 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12448 ≤ 2 * (370 / 100 : ℝ) / 12448 := by
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
    (completeRAData (tableEnvelope C) 12448 161).locationBound 12448 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12448 161).energyBound 12448 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12448 161) (d.f1 12448 161) d.f2 ≤
      32 * (((2409092003 / 500000000000000000) : ℝ) + (1607427823 / 1000000000000000000) + (386345859 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12448 161) (d.w1 12448 161)
      (d.w2 12448 161) ≤
      32 * (((121675609 / 6250000000000000000) : ℝ) + (1385117943 / 100000000000000000000) + (50608779 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12448 161) (d.f1 12448 161) d.f2 ≤
      ((2409092003 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2409092003 / 500000000000000000)) * ((1607427823 / 1000000000000000000)) * (126 / 100) +
      2 * (((1607427823 / 1000000000000000000)) ^ 2 + 2 * ((2409092003 / 500000000000000000)) * ((386345859 / 1000000000000000000))) +
      6 * ((1607427823 / 1000000000000000000)) * ((386345859 / 1000000000000000000)) * (126 / 100) + 8 * ((386345859 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12448 161) (d.f1 12448 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12448 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12448 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12448 161) (d.f1 12448 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12448 161) (d.w1 12448 161) (d.w2 12448 161)
  have hwexpr0 : 0 ≤ d.w0 12448 161 + d.w1 12448 161 * √(π / 2) +
      2 * d.w2 12448 161 + energyR16 12448 *
      radiusPolynomialRoot16 (d.w0 12448 161) (d.w1 12448 161) (d.w2 12448 161) := by
    positivity
  constructor
  · change (12448 : ℝ) ^ 8 * (mA 12448 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12448 161) (d.f1 12448 161) d.f2 + locationR16 12448 *
        radiusPolynomialRoot16 (d.f0 12448 161) (d.f1 12448 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12448 : ℝ) ^ 8 * (mA 12448 : ℝ) ^ 8 *
        ((((2409092003 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2409092003 / 500000000000000000)) * ((1607427823 / 1000000000000000000)) * (126 / 100) +
          2 * (((1607427823 / 1000000000000000000)) ^ 2 + 2 * ((2409092003 / 500000000000000000)) * ((386345859 / 1000000000000000000))) +
          6 * ((1607427823 / 1000000000000000000)) * ((386345859 / 1000000000000000000)) * (126 / 100) + 8 * ((386345859 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12448) *
          (32 * (((2409092003 / 500000000000000000) : ℝ) + (1607427823 / 1000000000000000000) + (386345859 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12448 : ℝ) ^ 16 *
      (d.w0 12448 161 + d.w1 12448 161 * √(π / 2) + 2 * d.w2 12448 161 +
        energyR16 12448 * radiusPolynomialRoot16 (d.w0 12448 161) (d.w1 12448 161)
          (d.w2 12448 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12448 : ℝ) ^ 16 *
        (((121675609 / 6250000000000000000) : ℝ) + ((1385117943 / 100000000000000000000)) * (126 / 100) + 2 * ((50608779 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12448) *
          (32 * (((121675609 / 6250000000000000000) : ℝ) + (1385117943 / 100000000000000000000) + (50608779 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12448

/-! A coarse bound on the actual paper statistics constant at dimension 12449. -/
namespace BstLean.Part266.Row12449
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12447 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12447 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12447 128 ≤ (12701 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12701 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12449) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12449 : ℕ))
    (by norm_num : (12449 : ℕ) ≤ 16384)
  have ht : paperTail256 12449 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12449 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12449 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12449 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12449 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12449 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12447 128 * √(2 / (12449 : ℝ)) *
      (√(12449 : ℝ) + paperT0 12449 + paperTail256 12449) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12449 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12449 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12449 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12447 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12447 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12449 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12449

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12449
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12449 (61 / 100) 161 (17 / (100 * 12449)) (26 / (10 * 12449)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12449 (61 / 100) 161 (17 / (100 * 12449)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (505960013 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1625704941 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3003643521 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12449 / 12449 * (61 / 100)) ^ 4 * inverseRadius8 (12449 - 1) /
            envelopeGap 12449 (61 / 100) 161 (17 / (100 * 12449)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12449

namespace BstLean.Part266.Row12449
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12449 161 ≤ (963442961 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12449 161 ≤ (803552323 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (96567057 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12449 161 ≤ (973170137 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12449 161 ≤ (1384784001 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12449 161 ≤ (505965833 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (505960013 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (505960013 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1625704941 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3003643521 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((923841 / 250000000) : ℝ) ≤ √(17 / (100 * 12449) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12449) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2249355493 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40320031511 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12449) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12449) ≤ (1775009 / 15625000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12449) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12449 * (161 : ℝ) ^ 2 + 26 / (10 * 12449) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12449) : ℝ)) (tA 12449 * 161 ^ 2 + 26 / (10 * 12449)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((923841 / 250000000))) * ((505960013 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((923841 / 250000000)) ^ 3) * ((1625704941 / 1000000000000000000000000))) + ((3003643521 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((923841 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12449) : ℝ)) d.D d.V d.P (√(tA 12449) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((923841 / 250000000)) ^ 2 * (((2249355493 / 1000000000000000)) * ((40320031511 / 1000000000000000000)))) + ((3003643521 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12449) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((923841 / 250000000)) * ((505960013 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12449) : ℝ)) (tA 12449 * 161 ^ 2 + 26 / (10 * 12449)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((505960013 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((923841 / 250000000)) ^ 2) * ((1625704941 / 1000000000000000000000000)) + ((3003643521 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12449) : ℝ)) (√(26 / (10 * 12449) : ℝ)) d.D d.V d.P (√(tA 12449) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((923841 / 250000000)) * (((2249355493 / 1000000000000000)) * ((40320031511 / 1000000000000000000))) + ((3003643521 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12449) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((505960013 / 100000000000000000000) : ℝ) + ((3003643521 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12449

namespace BstLean.Part266.Row12449
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12449 161 ∧
    0 ≤ (tableEnvelope C).f1 12449 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12449 161 ∧
    0 ≤ (tableEnvelope C).w1 12449 161 ∧ 0 ≤ (tableEnvelope C).w2 12449 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12449 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12449 161 ∧ 0 ≤ d.f1 12449 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12449 161 ∧ 0 ≤ d.w1 12449 161 ∧ 0 ≤ d.w2 12449 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12449 ≤ 2 * (228 / 100 : ℝ) / 12449 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12449 ≤ 2 * (370 / 100 : ℝ) / 12449 := by
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
    (completeRAData (tableEnvelope C) 12449 161).locationBound 12449 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12449 161).energyBound 12449 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12449 161) (d.f1 12449 161) d.f2 ≤
      32 * (((963442961 / 200000000000000000) : ℝ) + (803552323 / 500000000000000000) + (96567057 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12449 161) (d.w1 12449 161)
      (d.w2 12449 161) ≤
      32 * (((973170137 / 50000000000000000000) : ℝ) + (1384784001 / 100000000000000000000) + (505965833 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12449 161) (d.f1 12449 161) d.f2 ≤
      ((963442961 / 200000000000000000) : ℝ) ^ 2 + 2 * ((963442961 / 200000000000000000)) * ((803552323 / 500000000000000000)) * (126 / 100) +
      2 * (((803552323 / 500000000000000000)) ^ 2 + 2 * ((963442961 / 200000000000000000)) * ((96567057 / 250000000000000000))) +
      6 * ((803552323 / 500000000000000000)) * ((96567057 / 250000000000000000)) * (126 / 100) + 8 * ((96567057 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12449 161) (d.f1 12449 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12449 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12449 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12449 161) (d.f1 12449 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12449 161) (d.w1 12449 161) (d.w2 12449 161)
  have hwexpr0 : 0 ≤ d.w0 12449 161 + d.w1 12449 161 * √(π / 2) +
      2 * d.w2 12449 161 + energyR16 12449 *
      radiusPolynomialRoot16 (d.w0 12449 161) (d.w1 12449 161) (d.w2 12449 161) := by
    positivity
  constructor
  · change (12449 : ℝ) ^ 8 * (mA 12449 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12449 161) (d.f1 12449 161) d.f2 + locationR16 12449 *
        radiusPolynomialRoot16 (d.f0 12449 161) (d.f1 12449 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12449 : ℝ) ^ 8 * (mA 12449 : ℝ) ^ 8 *
        ((((963442961 / 200000000000000000) : ℝ) ^ 2 + 2 * ((963442961 / 200000000000000000)) * ((803552323 / 500000000000000000)) * (126 / 100) +
          2 * (((803552323 / 500000000000000000)) ^ 2 + 2 * ((963442961 / 200000000000000000)) * ((96567057 / 250000000000000000))) +
          6 * ((803552323 / 500000000000000000)) * ((96567057 / 250000000000000000)) * (126 / 100) + 8 * ((96567057 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12449) *
          (32 * (((963442961 / 200000000000000000) : ℝ) + (803552323 / 500000000000000000) + (96567057 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12449 : ℝ) ^ 16 *
      (d.w0 12449 161 + d.w1 12449 161 * √(π / 2) + 2 * d.w2 12449 161 +
        energyR16 12449 * radiusPolynomialRoot16 (d.w0 12449 161) (d.w1 12449 161)
          (d.w2 12449 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12449 : ℝ) ^ 16 *
        (((973170137 / 50000000000000000000) : ℝ) + ((1384784001 / 100000000000000000000)) * (126 / 100) + 2 * ((505965833 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12449) *
          (32 * (((973170137 / 50000000000000000000) : ℝ) + (1384784001 / 100000000000000000000) + (505965833 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12449
