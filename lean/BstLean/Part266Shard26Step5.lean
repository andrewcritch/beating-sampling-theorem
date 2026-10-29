import BstLean.Part266Shard26Step4


/-! A coarse bound on the actual paper statistics constant at dimension 13000. -/
namespace BstLean.Part266.Row13000
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12998 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12998 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12998 128 ≤ (13252 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13252 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13000) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13000 : ℕ))
    (by norm_num : (13000 : ℕ) ≤ 16384)
  have ht : paperTail256 13000 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13000 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13000 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13000 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13000 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13000 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 12998 128 * √(2 / (13000 : ℝ)) *
      (√(13000 : ℝ) + paperT0 13000 + paperTail256 13000) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13000 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13000 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13000 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12998 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12998 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13000 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13000

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13000
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13000 (61 / 100) 165 (17 / (100 * 13000)) (26 / (10 * 13000)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13000 (61 / 100) 165 (17 / (100 * 13000)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (55538813 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1367109263 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4241838567 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13000 / 13000 * (61 / 100)) ^ 4 * inverseRadius8 (13000 - 1) /
            envelopeGap 13000 (61 / 100) 165 (17 / (100 * 13000)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13000

namespace BstLean.Part266.Row13000
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13000 165 ≤ (4322859461 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13000 165 ≤ (144217893 / 100000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (173314109 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13000 165 ≤ (1709185667 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13000 165 ≤ (304013223 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 13000 165 ≤ (222157307 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (55538813 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (55538813 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1367109263 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4241838567 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1808101 / 500000000) : ℝ) ≤ √(17 / (100 * 13000) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13000) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (263483427 / 125000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1155451271 / 31250000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13000) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13000) ≤ (108785659 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13000) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13000 * (165 : ℝ) ^ 2 + 26 / (10 * 13000) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13000) : ℝ)) (tA 13000 * 165 ^ 2 + 26 / (10 * 13000)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1808101 / 500000000))) * ((55538813 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1808101 / 500000000)) ^ 3) * ((1367109263 / 1000000000000000000000000))) + ((4241838567 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1808101 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13000) : ℝ)) d.D d.V d.P (√(tA 13000) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1808101 / 500000000)) ^ 2 * (((263483427 / 125000000000000)) * ((1155451271 / 31250000000000000)))) + ((4241838567 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13000) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1808101 / 500000000)) * ((55538813 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13000) : ℝ)) (tA 13000 * 165 ^ 2 + 26 / (10 * 13000)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((55538813 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1808101 / 500000000)) ^ 2) * ((1367109263 / 1000000000000000000000000)) + ((4241838567 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13000) : ℝ)) (√(26 / (10 * 13000) : ℝ)) d.D d.V d.P (√(tA 13000) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1808101 / 500000000)) * (((263483427 / 125000000000000)) * ((1155451271 / 31250000000000000))) + ((4241838567 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13000) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((55538813 / 12500000000000000000) : ℝ) + ((4241838567 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13000

namespace BstLean.Part266.Row13000
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13000 165 ∧
    0 ≤ (tableEnvelope C).f1 13000 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13000 165 ∧
    0 ≤ (tableEnvelope C).w1 13000 165 ∧ 0 ≤ (tableEnvelope C).w2 13000 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13000 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13000 165 ∧ 0 ≤ d.f1 13000 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13000 165 ∧ 0 ≤ d.w1 13000 165 ∧ 0 ≤ d.w2 13000 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13000 ≤ 2 * (228 / 100 : ℝ) / 13000 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13000 ≤ 2 * (370 / 100 : ℝ) / 13000 := by
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
    (completeRAData (tableEnvelope C) 13000 165).locationBound 13000 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13000 165).energyBound 13000 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13000 165) (d.f1 13000 165) d.f2 ≤
      32 * (((4322859461 / 1000000000000000000) : ℝ) + (144217893 / 100000000000000000) + (173314109 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13000 165) (d.w1 13000 165)
      (d.w2 13000 165) ≤
      32 * (((1709185667 / 100000000000000000000) : ℝ) + (304013223 / 25000000000000000000) + (222157307 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13000 165) (d.f1 13000 165) d.f2 ≤
      ((4322859461 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4322859461 / 1000000000000000000)) * ((144217893 / 100000000000000000)) * (126 / 100) +
      2 * (((144217893 / 100000000000000000)) ^ 2 + 2 * ((4322859461 / 1000000000000000000)) * ((173314109 / 500000000000000000))) +
      6 * ((144217893 / 100000000000000000)) * ((173314109 / 500000000000000000)) * (126 / 100) + 8 * ((173314109 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13000 165) (d.f1 13000 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13000 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13000 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13000 165) (d.f1 13000 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13000 165) (d.w1 13000 165) (d.w2 13000 165)
  have hwexpr0 : 0 ≤ d.w0 13000 165 + d.w1 13000 165 * √(π / 2) +
      2 * d.w2 13000 165 + energyR16 13000 *
      radiusPolynomialRoot16 (d.w0 13000 165) (d.w1 13000 165) (d.w2 13000 165) := by
    positivity
  constructor
  · change (13000 : ℝ) ^ 8 * (mA 13000 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13000 165) (d.f1 13000 165) d.f2 + locationR16 13000 *
        radiusPolynomialRoot16 (d.f0 13000 165) (d.f1 13000 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13000 : ℝ) ^ 8 * (mA 13000 : ℝ) ^ 8 *
        ((((4322859461 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4322859461 / 1000000000000000000)) * ((144217893 / 100000000000000000)) * (126 / 100) +
          2 * (((144217893 / 100000000000000000)) ^ 2 + 2 * ((4322859461 / 1000000000000000000)) * ((173314109 / 500000000000000000))) +
          6 * ((144217893 / 100000000000000000)) * ((173314109 / 500000000000000000)) * (126 / 100) + 8 * ((173314109 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13000) *
          (32 * (((4322859461 / 1000000000000000000) : ℝ) + (144217893 / 100000000000000000) + (173314109 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13000 : ℝ) ^ 16 *
      (d.w0 13000 165 + d.w1 13000 165 * √(π / 2) + 2 * d.w2 13000 165 +
        energyR16 13000 * radiusPolynomialRoot16 (d.w0 13000 165) (d.w1 13000 165)
          (d.w2 13000 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13000 : ℝ) ^ 16 *
        (((1709185667 / 100000000000000000000) : ℝ) + ((304013223 / 25000000000000000000)) * (126 / 100) + 2 * ((222157307 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13000) *
          (32 * (((1709185667 / 100000000000000000000) : ℝ) + (304013223 / 25000000000000000000) + (222157307 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13000

/-! A coarse bound on the actual paper statistics constant at dimension 13001. -/
namespace BstLean.Part266.Row13001
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12999 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12999 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12999 128 ≤ (13253 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13253 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13001) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13001 : ℕ))
    (by norm_num : (13001 : ℕ) ≤ 16384)
  have ht : paperTail256 13001 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13001 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13001 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13001 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13001 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13001 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 12999 128 * √(2 / (13001 : ℝ)) *
      (√(13001 : ℝ) + paperT0 13001 + paperTail256 13001) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13001 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13001 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13001 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12999 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12999 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13001 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13001

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13001
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13001 (61 / 100) 165 (17 / (100 * 13001)) (26 / (10 * 13001)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13001 (61 / 100) 165 (17 / (100 * 13001)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (222103991 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1366688679 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4239204263 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13001 / 13001 * (61 / 100)) ^ 4 * inverseRadius8 (13001 - 1) /
            envelopeGap 13001 (61 / 100) 165 (17 / (100 * 13001)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13001

namespace BstLean.Part266.Row13001
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13001 165 ≤ (4322027939 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13001 165 ≤ (360475387 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (346561557 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13001 165 ≤ (1708791227 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13001 165 ≤ (1215772269 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13001 165 ≤ (444212089 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (222103991 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (222103991 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1366688679 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4239204263 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3616063 / 1000000000) : ℝ) ≤ √(17 / (100 * 13001) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13001) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2107624213 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18484376369 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13001) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13001) ≤ (27194323 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13001) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13001 * (165 : ℝ) ^ 2 + 26 / (10 * 13001) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13001) : ℝ)) (tA 13001 * 165 ^ 2 + 26 / (10 * 13001)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3616063 / 1000000000))) * ((222103991 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3616063 / 1000000000)) ^ 3) * ((1366688679 / 1000000000000000000000000))) + ((4239204263 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3616063 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13001) : ℝ)) d.D d.V d.P (√(tA 13001) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3616063 / 1000000000)) ^ 2 * (((2107624213 / 1000000000000000)) * ((18484376369 / 500000000000000000)))) + ((4239204263 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13001) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3616063 / 1000000000)) * ((222103991 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13001) : ℝ)) (tA 13001 * 165 ^ 2 + 26 / (10 * 13001)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((222103991 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3616063 / 1000000000)) ^ 2) * ((1366688679 / 1000000000000000000000000)) + ((4239204263 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13001) : ℝ)) (√(26 / (10 * 13001) : ℝ)) d.D d.V d.P (√(tA 13001) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3616063 / 1000000000)) * (((2107624213 / 1000000000000000)) * ((18484376369 / 500000000000000000))) + ((4239204263 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13001) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((222103991 / 50000000000000000000) : ℝ) + ((4239204263 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13001

namespace BstLean.Part266.Row13001
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13001 165 ∧
    0 ≤ (tableEnvelope C).f1 13001 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13001 165 ∧
    0 ≤ (tableEnvelope C).w1 13001 165 ∧ 0 ≤ (tableEnvelope C).w2 13001 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13001 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13001 165 ∧ 0 ≤ d.f1 13001 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13001 165 ∧ 0 ≤ d.w1 13001 165 ∧ 0 ≤ d.w2 13001 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13001 ≤ 2 * (228 / 100 : ℝ) / 13001 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13001 ≤ 2 * (370 / 100 : ℝ) / 13001 := by
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
    (completeRAData (tableEnvelope C) 13001 165).locationBound 13001 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13001 165).energyBound 13001 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13001 165) (d.f1 13001 165) d.f2 ≤
      32 * (((4322027939 / 1000000000000000000) : ℝ) + (360475387 / 250000000000000000) + (346561557 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13001 165) (d.w1 13001 165)
      (d.w2 13001 165) ≤
      32 * (((1708791227 / 100000000000000000000) : ℝ) + (1215772269 / 100000000000000000000) + (444212089 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13001 165) (d.f1 13001 165) d.f2 ≤
      ((4322027939 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4322027939 / 1000000000000000000)) * ((360475387 / 250000000000000000)) * (126 / 100) +
      2 * (((360475387 / 250000000000000000)) ^ 2 + 2 * ((4322027939 / 1000000000000000000)) * ((346561557 / 1000000000000000000))) +
      6 * ((360475387 / 250000000000000000)) * ((346561557 / 1000000000000000000)) * (126 / 100) + 8 * ((346561557 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13001 165) (d.f1 13001 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13001 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13001 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13001 165) (d.f1 13001 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13001 165) (d.w1 13001 165) (d.w2 13001 165)
  have hwexpr0 : 0 ≤ d.w0 13001 165 + d.w1 13001 165 * √(π / 2) +
      2 * d.w2 13001 165 + energyR16 13001 *
      radiusPolynomialRoot16 (d.w0 13001 165) (d.w1 13001 165) (d.w2 13001 165) := by
    positivity
  constructor
  · change (13001 : ℝ) ^ 8 * (mA 13001 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13001 165) (d.f1 13001 165) d.f2 + locationR16 13001 *
        radiusPolynomialRoot16 (d.f0 13001 165) (d.f1 13001 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13001 : ℝ) ^ 8 * (mA 13001 : ℝ) ^ 8 *
        ((((4322027939 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4322027939 / 1000000000000000000)) * ((360475387 / 250000000000000000)) * (126 / 100) +
          2 * (((360475387 / 250000000000000000)) ^ 2 + 2 * ((4322027939 / 1000000000000000000)) * ((346561557 / 1000000000000000000))) +
          6 * ((360475387 / 250000000000000000)) * ((346561557 / 1000000000000000000)) * (126 / 100) + 8 * ((346561557 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13001) *
          (32 * (((4322027939 / 1000000000000000000) : ℝ) + (360475387 / 250000000000000000) + (346561557 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13001 : ℝ) ^ 16 *
      (d.w0 13001 165 + d.w1 13001 165 * √(π / 2) + 2 * d.w2 13001 165 +
        energyR16 13001 * radiusPolynomialRoot16 (d.w0 13001 165) (d.w1 13001 165)
          (d.w2 13001 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13001 : ℝ) ^ 16 *
        (((1708791227 / 100000000000000000000) : ℝ) + ((1215772269 / 100000000000000000000)) * (126 / 100) + 2 * ((444212089 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13001) *
          (32 * (((1708791227 / 100000000000000000000) : ℝ) + (1215772269 / 100000000000000000000) + (444212089 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13001

/-! A coarse bound on the actual paper statistics constant at dimension 13002. -/
namespace BstLean.Part266.Row13002
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13000 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13000 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13000 128 ≤ (13254 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13254 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13002) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13002 : ℕ))
    (by norm_num : (13002 : ℕ) ≤ 16384)
  have ht : paperTail256 13002 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13002 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13002 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13002 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13002 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13002 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13000 128 * √(2 / (13002 : ℝ)) *
      (√(13002 : ℝ) + paperT0 13002 + paperTail256 13002) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13002 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13002 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13002 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13000 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13000 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13002 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13002

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13002
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13002 (61 / 100) 165 (17 / (100 * 13002)) (26 / (10 * 13002)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13002 (61 / 100) 165 (17 / (100 * 13002)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (444105491 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (42695883 / 31250000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2118285901 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13002 / 13002 * (61 / 100)) ^ 4 * inverseRadius8 (13002 - 1) /
            envelopeGap 13002 (61 / 100) 165 (17 / (100 * 13002)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13002

namespace BstLean.Part266.Row13002
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13002 165 ≤ (2160598347 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13002 165 ≤ (360406063 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (173247457 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13002 165 ≤ (1708396919 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13002 165 ≤ (243098347 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 13002 165 ≤ (88821919 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (444105491 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (444105491 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (42695883 / 31250000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2118285901 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((903981 / 250000000) : ℝ) ≤ √(17 / (100 * 13002) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13002) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (421476211 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36963066107 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13002) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13002) ≤ (4350757 / 40000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13002) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13002 * (165 : ℝ) ^ 2 + 26 / (10 * 13002) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13002) : ℝ)) (tA 13002 * 165 ^ 2 + 26 / (10 * 13002)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((903981 / 250000000))) * ((444105491 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((903981 / 250000000)) ^ 3) * ((42695883 / 31250000000000000000000))) + ((2118285901 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((903981 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13002) : ℝ)) d.D d.V d.P (√(tA 13002) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((903981 / 250000000)) ^ 2 * (((421476211 / 200000000000000)) * ((36963066107 / 1000000000000000000)))) + ((2118285901 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13002) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((903981 / 250000000)) * ((444105491 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13002) : ℝ)) (tA 13002 * 165 ^ 2 + 26 / (10 * 13002)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((444105491 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((903981 / 250000000)) ^ 2) * ((42695883 / 31250000000000000000000)) + ((2118285901 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13002) : ℝ)) (√(26 / (10 * 13002) : ℝ)) d.D d.V d.P (√(tA 13002) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((903981 / 250000000)) * (((421476211 / 200000000000000)) * ((36963066107 / 1000000000000000000))) + ((2118285901 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13002) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((444105491 / 100000000000000000000) : ℝ) + ((2118285901 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13002

namespace BstLean.Part266.Row13002
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13002 165 ∧
    0 ≤ (tableEnvelope C).f1 13002 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13002 165 ∧
    0 ≤ (tableEnvelope C).w1 13002 165 ∧ 0 ≤ (tableEnvelope C).w2 13002 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13002 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13002 165 ∧ 0 ≤ d.f1 13002 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13002 165 ∧ 0 ≤ d.w1 13002 165 ∧ 0 ≤ d.w2 13002 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13002 ≤ 2 * (228 / 100 : ℝ) / 13002 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13002 ≤ 2 * (370 / 100 : ℝ) / 13002 := by
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
    (completeRAData (tableEnvelope C) 13002 165).locationBound 13002 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13002 165).energyBound 13002 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13002 165) (d.f1 13002 165) d.f2 ≤
      32 * (((2160598347 / 500000000000000000) : ℝ) + (360406063 / 250000000000000000) + (173247457 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13002 165) (d.w1 13002 165)
      (d.w2 13002 165) ≤
      32 * (((1708396919 / 100000000000000000000) : ℝ) + (243098347 / 20000000000000000000) + (88821919 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13002 165) (d.f1 13002 165) d.f2 ≤
      ((2160598347 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2160598347 / 500000000000000000)) * ((360406063 / 250000000000000000)) * (126 / 100) +
      2 * (((360406063 / 250000000000000000)) ^ 2 + 2 * ((2160598347 / 500000000000000000)) * ((173247457 / 500000000000000000))) +
      6 * ((360406063 / 250000000000000000)) * ((173247457 / 500000000000000000)) * (126 / 100) + 8 * ((173247457 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13002 165) (d.f1 13002 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13002 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13002 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13002 165) (d.f1 13002 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13002 165) (d.w1 13002 165) (d.w2 13002 165)
  have hwexpr0 : 0 ≤ d.w0 13002 165 + d.w1 13002 165 * √(π / 2) +
      2 * d.w2 13002 165 + energyR16 13002 *
      radiusPolynomialRoot16 (d.w0 13002 165) (d.w1 13002 165) (d.w2 13002 165) := by
    positivity
  constructor
  · change (13002 : ℝ) ^ 8 * (mA 13002 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13002 165) (d.f1 13002 165) d.f2 + locationR16 13002 *
        radiusPolynomialRoot16 (d.f0 13002 165) (d.f1 13002 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13002 : ℝ) ^ 8 * (mA 13002 : ℝ) ^ 8 *
        ((((2160598347 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2160598347 / 500000000000000000)) * ((360406063 / 250000000000000000)) * (126 / 100) +
          2 * (((360406063 / 250000000000000000)) ^ 2 + 2 * ((2160598347 / 500000000000000000)) * ((173247457 / 500000000000000000))) +
          6 * ((360406063 / 250000000000000000)) * ((173247457 / 500000000000000000)) * (126 / 100) + 8 * ((173247457 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13002) *
          (32 * (((2160598347 / 500000000000000000) : ℝ) + (360406063 / 250000000000000000) + (173247457 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13002 : ℝ) ^ 16 *
      (d.w0 13002 165 + d.w1 13002 165 * √(π / 2) + 2 * d.w2 13002 165 +
        energyR16 13002 * radiusPolynomialRoot16 (d.w0 13002 165) (d.w1 13002 165)
          (d.w2 13002 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13002 : ℝ) ^ 16 *
        (((1708396919 / 100000000000000000000) : ℝ) + ((243098347 / 20000000000000000000)) * (126 / 100) + 2 * ((88821919 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13002) *
          (32 * (((1708396919 / 100000000000000000000) : ℝ) + (243098347 / 20000000000000000000) + (88821919 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13002

/-! A coarse bound on the actual paper statistics constant at dimension 13003. -/
namespace BstLean.Part266.Row13003
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13001 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13001 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13001 128 ≤ (13255 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13255 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13003) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13003 : ℕ))
    (by norm_num : (13003 : ℕ) ≤ 16384)
  have ht : paperTail256 13003 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13003 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13003 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13003 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13003 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13003 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13001 128 * √(2 / (13003 : ℝ)) *
      (√(13003 : ℝ) + paperT0 13003 + paperTail256 13003) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13003 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13003 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13003 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13001 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13001 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13003 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13003

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13003
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13003 (61 / 100) 165 (17 / (100 * 13003)) (26 / (10 * 13003)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13003 (61 / 100) 165 (17 / (100 * 13003)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (444003031 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (273169599 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4233941181 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13003 / 13003 * (61 / 100)) ^ 4 * inverseRadius8 (13003 - 1) /
            envelopeGap 13003 (61 / 100) 165 (17 / (100 * 13003)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13003

namespace BstLean.Part266.Row13003
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13003 165 ≤ (4320365729 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13003 165 ≤ (1441347043 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (346428291 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13003 165 ≤ (854001371 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13003 165 ≤ (1215211293 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13003 165 ≤ (444007133 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (444003031 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (444003031 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (273169599 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4233941181 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((723157 / 200000000) : ℝ) ≤ √(17 / (100 * 13003) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13003) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2107137943 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4619672599 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13003) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13003) ≤ (108760561 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13003) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13003 * (165 : ℝ) ^ 2 + 26 / (10 * 13003) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13003) : ℝ)) (tA 13003 * 165 ^ 2 + 26 / (10 * 13003)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((723157 / 200000000))) * ((444003031 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((723157 / 200000000)) ^ 3) * ((273169599 / 200000000000000000000000))) + ((4233941181 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((723157 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13003) : ℝ)) d.D d.V d.P (√(tA 13003) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((723157 / 200000000)) ^ 2 * (((2107137943 / 1000000000000000)) * ((4619672599 / 125000000000000000)))) + ((4233941181 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13003) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((723157 / 200000000)) * ((444003031 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13003) : ℝ)) (tA 13003 * 165 ^ 2 + 26 / (10 * 13003)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((444003031 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((723157 / 200000000)) ^ 2) * ((273169599 / 200000000000000000000000)) + ((4233941181 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13003) : ℝ)) (√(26 / (10 * 13003) : ℝ)) d.D d.V d.P (√(tA 13003) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((723157 / 200000000)) * (((2107137943 / 1000000000000000)) * ((4619672599 / 125000000000000000))) + ((4233941181 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13003) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((444003031 / 100000000000000000000) : ℝ) + ((4233941181 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13003

namespace BstLean.Part266.Row13003
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13003 165 ∧
    0 ≤ (tableEnvelope C).f1 13003 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13003 165 ∧
    0 ≤ (tableEnvelope C).w1 13003 165 ∧ 0 ≤ (tableEnvelope C).w2 13003 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13003 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13003 165 ∧ 0 ≤ d.f1 13003 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13003 165 ∧ 0 ≤ d.w1 13003 165 ∧ 0 ≤ d.w2 13003 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13003 ≤ 2 * (228 / 100 : ℝ) / 13003 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13003 ≤ 2 * (370 / 100 : ℝ) / 13003 := by
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
    (completeRAData (tableEnvelope C) 13003 165).locationBound 13003 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13003 165).energyBound 13003 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13003 165) (d.f1 13003 165) d.f2 ≤
      32 * (((4320365729 / 1000000000000000000) : ℝ) + (1441347043 / 1000000000000000000) + (346428291 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13003 165) (d.w1 13003 165)
      (d.w2 13003 165) ≤
      32 * (((854001371 / 50000000000000000000) : ℝ) + (1215211293 / 100000000000000000000) + (444007133 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13003 165) (d.f1 13003 165) d.f2 ≤
      ((4320365729 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4320365729 / 1000000000000000000)) * ((1441347043 / 1000000000000000000)) * (126 / 100) +
      2 * (((1441347043 / 1000000000000000000)) ^ 2 + 2 * ((4320365729 / 1000000000000000000)) * ((346428291 / 1000000000000000000))) +
      6 * ((1441347043 / 1000000000000000000)) * ((346428291 / 1000000000000000000)) * (126 / 100) + 8 * ((346428291 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13003 165) (d.f1 13003 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13003 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13003 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13003 165) (d.f1 13003 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13003 165) (d.w1 13003 165) (d.w2 13003 165)
  have hwexpr0 : 0 ≤ d.w0 13003 165 + d.w1 13003 165 * √(π / 2) +
      2 * d.w2 13003 165 + energyR16 13003 *
      radiusPolynomialRoot16 (d.w0 13003 165) (d.w1 13003 165) (d.w2 13003 165) := by
    positivity
  constructor
  · change (13003 : ℝ) ^ 8 * (mA 13003 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13003 165) (d.f1 13003 165) d.f2 + locationR16 13003 *
        radiusPolynomialRoot16 (d.f0 13003 165) (d.f1 13003 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13003 : ℝ) ^ 8 * (mA 13003 : ℝ) ^ 8 *
        ((((4320365729 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4320365729 / 1000000000000000000)) * ((1441347043 / 1000000000000000000)) * (126 / 100) +
          2 * (((1441347043 / 1000000000000000000)) ^ 2 + 2 * ((4320365729 / 1000000000000000000)) * ((346428291 / 1000000000000000000))) +
          6 * ((1441347043 / 1000000000000000000)) * ((346428291 / 1000000000000000000)) * (126 / 100) + 8 * ((346428291 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13003) *
          (32 * (((4320365729 / 1000000000000000000) : ℝ) + (1441347043 / 1000000000000000000) + (346428291 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13003 : ℝ) ^ 16 *
      (d.w0 13003 165 + d.w1 13003 165 * √(π / 2) + 2 * d.w2 13003 165 +
        energyR16 13003 * radiusPolynomialRoot16 (d.w0 13003 165) (d.w1 13003 165)
          (d.w2 13003 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13003 : ℝ) ^ 16 *
        (((854001371 / 50000000000000000000) : ℝ) + ((1215211293 / 100000000000000000000)) * (126 / 100) + 2 * ((444007133 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13003) *
          (32 * (((854001371 / 50000000000000000000) : ℝ) + (1215211293 / 100000000000000000000) + (444007133 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13003

/-! A coarse bound on the actual paper statistics constant at dimension 13004. -/
namespace BstLean.Part266.Row13004
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13002 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13002 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13002 128 ≤ (13256 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13256 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13004) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13004 : ℕ))
    (by norm_num : (13004 : ℕ) ≤ 16384)
  have ht : paperTail256 13004 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13004 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13004 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13004 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13004 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13004 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13002 128 * √(2 / (13004 : ℝ)) *
      (√(13004 : ℝ) + paperT0 13004 + paperTail256 13004) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13004 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13004 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13004 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13002 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13002 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13004 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13004

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13004
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13004 (61 / 100) 165 (17 / (100 * 13004)) (26 / (10 * 13004)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13004 (61 / 100) 165 (17 / (100 * 13004)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (443900603 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (170678487 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (10578281 / 2500000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13004 / 13004 * (61 / 100)) ^ 4 * inverseRadius8 (13004 - 1) /
            envelopeGap 13004 (61 / 100) 165 (17 / (100 * 13004)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13004

namespace BstLean.Part266.Row13004
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13004 165 ≤ (1079883761 / 250000000000000000)
  f1 : (tableEnvelope C).f1 13004 165 ≤ (720534961 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (43295211 / 125000000000000000)
  w0 : (tableEnvelope C).w0 13004 165 ≤ (1707608699 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13004 165 ≤ (148307 / 12207031250000000)
  w2 : (tableEnvelope C).w2 13004 165 ≤ (221952351 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (443900603 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (443900603 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (170678487 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (10578281 / 2500000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1807823 / 500000000) : ℝ) ≤ √(17 / (100 * 13004) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13004) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2106894879 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7390339359 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13004) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13004) ≤ (108752197 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13004) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13004 * (165 : ℝ) ^ 2 + 26 / (10 * 13004) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13004) : ℝ)) (tA 13004 * 165 ^ 2 + 26 / (10 * 13004)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1807823 / 500000000))) * ((443900603 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1807823 / 500000000)) ^ 3) * ((170678487 / 125000000000000000000000))) + ((10578281 / 2500000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1807823 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13004) : ℝ)) d.D d.V d.P (√(tA 13004) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1807823 / 500000000)) ^ 2 * (((2106894879 / 1000000000000000)) * ((7390339359 / 200000000000000000)))) + ((10578281 / 2500000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13004) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1807823 / 500000000)) * ((443900603 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13004) : ℝ)) (tA 13004 * 165 ^ 2 + 26 / (10 * 13004)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((443900603 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1807823 / 500000000)) ^ 2) * ((170678487 / 125000000000000000000000)) + ((10578281 / 2500000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13004) : ℝ)) (√(26 / (10 * 13004) : ℝ)) d.D d.V d.P (√(tA 13004) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1807823 / 500000000)) * (((2106894879 / 1000000000000000)) * ((7390339359 / 200000000000000000))) + ((10578281 / 2500000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13004) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((443900603 / 100000000000000000000) : ℝ) + ((10578281 / 2500000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13004

namespace BstLean.Part266.Row13004
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13004 165 ∧
    0 ≤ (tableEnvelope C).f1 13004 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13004 165 ∧
    0 ≤ (tableEnvelope C).w1 13004 165 ∧ 0 ≤ (tableEnvelope C).w2 13004 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13004 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13004 165 ∧ 0 ≤ d.f1 13004 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13004 165 ∧ 0 ≤ d.w1 13004 165 ∧ 0 ≤ d.w2 13004 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13004 ≤ 2 * (228 / 100 : ℝ) / 13004 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13004 ≤ 2 * (370 / 100 : ℝ) / 13004 := by
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
    (completeRAData (tableEnvelope C) 13004 165).locationBound 13004 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13004 165).energyBound 13004 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13004 165) (d.f1 13004 165) d.f2 ≤
      32 * (((1079883761 / 250000000000000000) : ℝ) + (720534961 / 500000000000000000) + (43295211 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13004 165) (d.w1 13004 165)
      (d.w2 13004 165) ≤
      32 * (((1707608699 / 100000000000000000000) : ℝ) + (148307 / 12207031250000000) + (221952351 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13004 165) (d.f1 13004 165) d.f2 ≤
      ((1079883761 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1079883761 / 250000000000000000)) * ((720534961 / 500000000000000000)) * (126 / 100) +
      2 * (((720534961 / 500000000000000000)) ^ 2 + 2 * ((1079883761 / 250000000000000000)) * ((43295211 / 125000000000000000))) +
      6 * ((720534961 / 500000000000000000)) * ((43295211 / 125000000000000000)) * (126 / 100) + 8 * ((43295211 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13004 165) (d.f1 13004 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13004 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13004 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13004 165) (d.f1 13004 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13004 165) (d.w1 13004 165) (d.w2 13004 165)
  have hwexpr0 : 0 ≤ d.w0 13004 165 + d.w1 13004 165 * √(π / 2) +
      2 * d.w2 13004 165 + energyR16 13004 *
      radiusPolynomialRoot16 (d.w0 13004 165) (d.w1 13004 165) (d.w2 13004 165) := by
    positivity
  constructor
  · change (13004 : ℝ) ^ 8 * (mA 13004 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13004 165) (d.f1 13004 165) d.f2 + locationR16 13004 *
        radiusPolynomialRoot16 (d.f0 13004 165) (d.f1 13004 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13004 : ℝ) ^ 8 * (mA 13004 : ℝ) ^ 8 *
        ((((1079883761 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1079883761 / 250000000000000000)) * ((720534961 / 500000000000000000)) * (126 / 100) +
          2 * (((720534961 / 500000000000000000)) ^ 2 + 2 * ((1079883761 / 250000000000000000)) * ((43295211 / 125000000000000000))) +
          6 * ((720534961 / 500000000000000000)) * ((43295211 / 125000000000000000)) * (126 / 100) + 8 * ((43295211 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13004) *
          (32 * (((1079883761 / 250000000000000000) : ℝ) + (720534961 / 500000000000000000) + (43295211 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13004 : ℝ) ^ 16 *
      (d.w0 13004 165 + d.w1 13004 165 * √(π / 2) + 2 * d.w2 13004 165 +
        energyR16 13004 * radiusPolynomialRoot16 (d.w0 13004 165) (d.w1 13004 165)
          (d.w2 13004 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13004 : ℝ) ^ 16 *
        (((1707608699 / 100000000000000000000) : ℝ) + ((148307 / 12207031250000000)) * (126 / 100) + 2 * ((221952351 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13004) *
          (32 * (((1707608699 / 100000000000000000000) : ℝ) + (148307 / 12207031250000000) + (221952351 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13004

/-! A coarse bound on the actual paper statistics constant at dimension 13005. -/
namespace BstLean.Part266.Row13005
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13003 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13003 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13003 128 ≤ (13257 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13257 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13005) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13005 : ℕ))
    (by norm_num : (13005 : ℕ) ≤ 16384)
  have ht : paperTail256 13005 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13005 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13005 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13005 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13005 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13005 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13003 128 * √(2 / (13005 : ℝ)) *
      (√(13005 : ℝ) + paperT0 13005 + paperTail256 13005) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13005 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13005 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13005 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13003 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13003 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13005 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13005

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13005
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13005 (61 / 100) 165 (17 / (100 * 13005)) (26 / (10 * 13005)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13005 (61 / 100) 165 (17 / (100 * 13005)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (221899103 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (682503979 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (264292841 / 62500000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13005 / 13005 * (61 / 100)) ^ 4 * inverseRadius8 (13005 - 1) /
            envelopeGap 13005 (61 / 100) 165 (17 / (100 * 13005)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13005

namespace BstLean.Part266.Row13005
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13005 165 ≤ (1079676159 / 250000000000000000)
  f1 : (tableEnvelope C).f1 13005 165 ≤ (1440792889 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (5410861 / 15625000000000000)
  w0 : (tableEnvelope C).w0 13005 165 ≤ (1707214787 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13005 165 ≤ (242930137 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 13005 165 ≤ (443802303 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (221899103 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (221899103 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (682503979 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (264292841 / 62500000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3615507 / 1000000000) : ℝ) ≤ √(17 / (100 * 13005) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13005) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2106651861 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18473007051 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13005) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13005) ≤ (21748767 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13005) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13005 * (165 : ℝ) ^ 2 + 26 / (10 * 13005) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13005) : ℝ)) (tA 13005 * 165 ^ 2 + 26 / (10 * 13005)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3615507 / 1000000000))) * ((221899103 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3615507 / 1000000000)) ^ 3) * ((682503979 / 500000000000000000000000))) + ((264292841 / 62500000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3615507 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13005) : ℝ)) d.D d.V d.P (√(tA 13005) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3615507 / 1000000000)) ^ 2 * (((2106651861 / 1000000000000000)) * ((18473007051 / 500000000000000000)))) + ((264292841 / 62500000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13005) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3615507 / 1000000000)) * ((221899103 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13005) : ℝ)) (tA 13005 * 165 ^ 2 + 26 / (10 * 13005)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((221899103 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3615507 / 1000000000)) ^ 2) * ((682503979 / 500000000000000000000000)) + ((264292841 / 62500000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13005) : ℝ)) (√(26 / (10 * 13005) : ℝ)) d.D d.V d.P (√(tA 13005) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3615507 / 1000000000)) * (((2106651861 / 1000000000000000)) * ((18473007051 / 500000000000000000))) + ((264292841 / 62500000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13005) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((221899103 / 50000000000000000000) : ℝ) + ((264292841 / 62500000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13005

namespace BstLean.Part266.Row13005
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13005 165 ∧
    0 ≤ (tableEnvelope C).f1 13005 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13005 165 ∧
    0 ≤ (tableEnvelope C).w1 13005 165 ∧ 0 ≤ (tableEnvelope C).w2 13005 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13005 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13005 165 ∧ 0 ≤ d.f1 13005 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13005 165 ∧ 0 ≤ d.w1 13005 165 ∧ 0 ≤ d.w2 13005 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13005 ≤ 2 * (228 / 100 : ℝ) / 13005 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13005 ≤ 2 * (370 / 100 : ℝ) / 13005 := by
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
    (completeRAData (tableEnvelope C) 13005 165).locationBound 13005 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13005 165).energyBound 13005 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13005 165) (d.f1 13005 165) d.f2 ≤
      32 * (((1079676159 / 250000000000000000) : ℝ) + (1440792889 / 1000000000000000000) + (5410861 / 15625000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13005 165) (d.w1 13005 165)
      (d.w2 13005 165) ≤
      32 * (((1707214787 / 100000000000000000000) : ℝ) + (242930137 / 20000000000000000000) + (443802303 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13005 165) (d.f1 13005 165) d.f2 ≤
      ((1079676159 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1079676159 / 250000000000000000)) * ((1440792889 / 1000000000000000000)) * (126 / 100) +
      2 * (((1440792889 / 1000000000000000000)) ^ 2 + 2 * ((1079676159 / 250000000000000000)) * ((5410861 / 15625000000000000))) +
      6 * ((1440792889 / 1000000000000000000)) * ((5410861 / 15625000000000000)) * (126 / 100) + 8 * ((5410861 / 15625000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13005 165) (d.f1 13005 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13005 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13005 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13005 165) (d.f1 13005 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13005 165) (d.w1 13005 165) (d.w2 13005 165)
  have hwexpr0 : 0 ≤ d.w0 13005 165 + d.w1 13005 165 * √(π / 2) +
      2 * d.w2 13005 165 + energyR16 13005 *
      radiusPolynomialRoot16 (d.w0 13005 165) (d.w1 13005 165) (d.w2 13005 165) := by
    positivity
  constructor
  · change (13005 : ℝ) ^ 8 * (mA 13005 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13005 165) (d.f1 13005 165) d.f2 + locationR16 13005 *
        radiusPolynomialRoot16 (d.f0 13005 165) (d.f1 13005 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13005 : ℝ) ^ 8 * (mA 13005 : ℝ) ^ 8 *
        ((((1079676159 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1079676159 / 250000000000000000)) * ((1440792889 / 1000000000000000000)) * (126 / 100) +
          2 * (((1440792889 / 1000000000000000000)) ^ 2 + 2 * ((1079676159 / 250000000000000000)) * ((5410861 / 15625000000000000))) +
          6 * ((1440792889 / 1000000000000000000)) * ((5410861 / 15625000000000000)) * (126 / 100) + 8 * ((5410861 / 15625000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13005) *
          (32 * (((1079676159 / 250000000000000000) : ℝ) + (1440792889 / 1000000000000000000) + (5410861 / 15625000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13005 : ℝ) ^ 16 *
      (d.w0 13005 165 + d.w1 13005 165 * √(π / 2) + 2 * d.w2 13005 165 +
        energyR16 13005 * radiusPolynomialRoot16 (d.w0 13005 165) (d.w1 13005 165)
          (d.w2 13005 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13005 : ℝ) ^ 16 *
        (((1707214787 / 100000000000000000000) : ℝ) + ((242930137 / 20000000000000000000)) * (126 / 100) + 2 * ((443802303 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13005) *
          (32 * (((1707214787 / 100000000000000000000) : ℝ) + (242930137 / 20000000000000000000) + (443802303 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13005

/-! A coarse bound on the actual paper statistics constant at dimension 13006. -/
namespace BstLean.Part266.Row13006
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13004 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13004 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13004 128 ≤ (13258 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13258 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13006) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13006 : ℕ))
    (by norm_num : (13006 : ℕ) ≤ 16384)
  have ht : paperTail256 13006 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13006 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13006 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13006 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13006 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13006 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13004 128 * √(2 / (13006 : ℝ)) *
      (√(13006 : ℝ) + paperT0 13006 + paperTail256 13006) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13006 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13006 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13006 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13004 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13004 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13006 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13006

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13006
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13006 (61 / 100) 165 (17 / (100 * 13006)) (26 / (10 * 13006)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13006 (61 / 100) 165 (17 / (100 * 13006)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (443695841 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1364588181 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4226060349 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13006 / 13006 * (61 / 100)) ^ 4 * inverseRadius8 (13006 - 1) /
            envelopeGap 13006 (61 / 100) 165 (17 / (100 * 13006)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13006

namespace BstLean.Part266.Row13006
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13006 165 ≤ (4317874507 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13006 165 ≤ (720257971 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (17311427 / 50000000000000000)
  w0 : (tableEnvelope C).w0 13006 165 ≤ (106676313 / 6250000000000000000)
  w1 : (tableEnvelope C).w1 13006 165 ≤ (607185259 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13006 165 ≤ (88739987 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (443695841 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (443695841 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1364588181 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4226060349 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((451921 / 125000000) : ℝ) ≤ √(17 / (100 * 13006) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13006) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (210640889 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18470166357 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13006) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13006) ≤ (54367737 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13006) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13006 * (165 : ℝ) ^ 2 + 26 / (10 * 13006) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13006) : ℝ)) (tA 13006 * 165 ^ 2 + 26 / (10 * 13006)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((451921 / 125000000))) * ((443695841 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((451921 / 125000000)) ^ 3) * ((1364588181 / 1000000000000000000000000))) + ((4226060349 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((451921 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13006) : ℝ)) d.D d.V d.P (√(tA 13006) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((451921 / 125000000)) ^ 2 * (((210640889 / 100000000000000)) * ((18470166357 / 500000000000000000)))) + ((4226060349 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13006) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((451921 / 125000000)) * ((443695841 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13006) : ℝ)) (tA 13006 * 165 ^ 2 + 26 / (10 * 13006)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((443695841 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((451921 / 125000000)) ^ 2) * ((1364588181 / 1000000000000000000000000)) + ((4226060349 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13006) : ℝ)) (√(26 / (10 * 13006) : ℝ)) d.D d.V d.P (√(tA 13006) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((451921 / 125000000)) * (((210640889 / 100000000000000)) * ((18470166357 / 500000000000000000))) + ((4226060349 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13006) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((443695841 / 100000000000000000000) : ℝ) + ((4226060349 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13006

namespace BstLean.Part266.Row13006
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13006 165 ∧
    0 ≤ (tableEnvelope C).f1 13006 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13006 165 ∧
    0 ≤ (tableEnvelope C).w1 13006 165 ∧ 0 ≤ (tableEnvelope C).w2 13006 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13006 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13006 165 ∧ 0 ≤ d.f1 13006 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13006 165 ∧ 0 ≤ d.w1 13006 165 ∧ 0 ≤ d.w2 13006 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13006 ≤ 2 * (228 / 100 : ℝ) / 13006 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13006 ≤ 2 * (370 / 100 : ℝ) / 13006 := by
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
    (completeRAData (tableEnvelope C) 13006 165).locationBound 13006 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13006 165).energyBound 13006 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13006 165) (d.f1 13006 165) d.f2 ≤
      32 * (((4317874507 / 1000000000000000000) : ℝ) + (720257971 / 500000000000000000) + (17311427 / 50000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13006 165) (d.w1 13006 165)
      (d.w2 13006 165) ≤
      32 * (((106676313 / 6250000000000000000) : ℝ) + (607185259 / 50000000000000000000) + (88739987 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13006 165) (d.f1 13006 165) d.f2 ≤
      ((4317874507 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4317874507 / 1000000000000000000)) * ((720257971 / 500000000000000000)) * (126 / 100) +
      2 * (((720257971 / 500000000000000000)) ^ 2 + 2 * ((4317874507 / 1000000000000000000)) * ((17311427 / 50000000000000000))) +
      6 * ((720257971 / 500000000000000000)) * ((17311427 / 50000000000000000)) * (126 / 100) + 8 * ((17311427 / 50000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13006 165) (d.f1 13006 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13006 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13006 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13006 165) (d.f1 13006 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13006 165) (d.w1 13006 165) (d.w2 13006 165)
  have hwexpr0 : 0 ≤ d.w0 13006 165 + d.w1 13006 165 * √(π / 2) +
      2 * d.w2 13006 165 + energyR16 13006 *
      radiusPolynomialRoot16 (d.w0 13006 165) (d.w1 13006 165) (d.w2 13006 165) := by
    positivity
  constructor
  · change (13006 : ℝ) ^ 8 * (mA 13006 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13006 165) (d.f1 13006 165) d.f2 + locationR16 13006 *
        radiusPolynomialRoot16 (d.f0 13006 165) (d.f1 13006 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13006 : ℝ) ^ 8 * (mA 13006 : ℝ) ^ 8 *
        ((((4317874507 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4317874507 / 1000000000000000000)) * ((720257971 / 500000000000000000)) * (126 / 100) +
          2 * (((720257971 / 500000000000000000)) ^ 2 + 2 * ((4317874507 / 1000000000000000000)) * ((17311427 / 50000000000000000))) +
          6 * ((720257971 / 500000000000000000)) * ((17311427 / 50000000000000000)) * (126 / 100) + 8 * ((17311427 / 50000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13006) *
          (32 * (((4317874507 / 1000000000000000000) : ℝ) + (720257971 / 500000000000000000) + (17311427 / 50000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13006 : ℝ) ^ 16 *
      (d.w0 13006 165 + d.w1 13006 165 * √(π / 2) + 2 * d.w2 13006 165 +
        energyR16 13006 * radiusPolynomialRoot16 (d.w0 13006 165) (d.w1 13006 165)
          (d.w2 13006 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13006 : ℝ) ^ 16 *
        (((106676313 / 6250000000000000000) : ℝ) + ((607185259 / 50000000000000000000)) * (126 / 100) + 2 * ((88739987 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13006) *
          (32 * (((106676313 / 6250000000000000000) : ℝ) + (607185259 / 50000000000000000000) + (88739987 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13006

/-! A coarse bound on the actual paper statistics constant at dimension 13007. -/
namespace BstLean.Part266.Row13007
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13005 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13005 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13005 128 ≤ (13259 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13259 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13007) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13007 : ℕ))
    (by norm_num : (13007 : ℕ) ≤ 16384)
  have ht : paperTail256 13007 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13007 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13007 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13007 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13007 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13007 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13005 128 * √(2 / (13007 : ℝ)) *
      (√(13007 : ℝ) + paperT0 13007 + paperTail256 13007) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13007 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13007 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13007 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13005 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13005 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13007 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13007

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13007
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13007 (61 / 100) 165 (17 / (100 * 13007)) (26 / (10 * 13007)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13007 (61 / 100) 165 (17 / (100 * 13007)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (110898377 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (682084283 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4223437077 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13007 / 13007 * (61 / 100)) ^ 4 * inverseRadius8 (13007 - 1) /
            envelopeGap 13007 (61 / 100) 165 (17 / (100 * 13007)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13007

namespace BstLean.Part266.Row13007
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13007 165 ≤ (4317044657 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13007 165 ≤ (360059771 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (69232399 / 200000000000000000)
  w0 : (tableEnvelope C).w0 13007 165 ≤ (1706427363 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13007 165 ≤ (303522611 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 13007 165 ≤ (554497 / 125000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (110898377 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (110898377 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (682084283 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4223437077 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3615229 / 1000000000) : ℝ) ≤ √(17 / (100 * 13007) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13007) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2106165967 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7386930529 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13007) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13007) ≤ (54363557 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13007) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13007 * (165 : ℝ) ^ 2 + 26 / (10 * 13007) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13007) : ℝ)) (tA 13007 * 165 ^ 2 + 26 / (10 * 13007)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3615229 / 1000000000))) * ((110898377 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3615229 / 1000000000)) ^ 3) * ((682084283 / 500000000000000000000000))) + ((4223437077 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3615229 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13007) : ℝ)) d.D d.V d.P (√(tA 13007) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3615229 / 1000000000)) ^ 2 * (((2106165967 / 1000000000000000)) * ((7386930529 / 200000000000000000)))) + ((4223437077 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13007) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3615229 / 1000000000)) * ((110898377 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13007) : ℝ)) (tA 13007 * 165 ^ 2 + 26 / (10 * 13007)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((110898377 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3615229 / 1000000000)) ^ 2) * ((682084283 / 500000000000000000000000)) + ((4223437077 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13007) : ℝ)) (√(26 / (10 * 13007) : ℝ)) d.D d.V d.P (√(tA 13007) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3615229 / 1000000000)) * (((2106165967 / 1000000000000000)) * ((7386930529 / 200000000000000000))) + ((4223437077 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13007) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((110898377 / 25000000000000000000) : ℝ) + ((4223437077 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13007

namespace BstLean.Part266.Row13007
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13007 165 ∧
    0 ≤ (tableEnvelope C).f1 13007 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13007 165 ∧
    0 ≤ (tableEnvelope C).w1 13007 165 ∧ 0 ≤ (tableEnvelope C).w2 13007 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13007 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13007 165 ∧ 0 ≤ d.f1 13007 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13007 165 ∧ 0 ≤ d.w1 13007 165 ∧ 0 ≤ d.w2 13007 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13007 ≤ 2 * (228 / 100 : ℝ) / 13007 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13007 ≤ 2 * (370 / 100 : ℝ) / 13007 := by
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
    (completeRAData (tableEnvelope C) 13007 165).locationBound 13007 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13007 165).energyBound 13007 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13007 165) (d.f1 13007 165) d.f2 ≤
      32 * (((4317044657 / 1000000000000000000) : ℝ) + (360059771 / 250000000000000000) + (69232399 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13007 165) (d.w1 13007 165)
      (d.w2 13007 165) ≤
      32 * (((1706427363 / 100000000000000000000) : ℝ) + (303522611 / 25000000000000000000) + (554497 / 125000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13007 165) (d.f1 13007 165) d.f2 ≤
      ((4317044657 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4317044657 / 1000000000000000000)) * ((360059771 / 250000000000000000)) * (126 / 100) +
      2 * (((360059771 / 250000000000000000)) ^ 2 + 2 * ((4317044657 / 1000000000000000000)) * ((69232399 / 200000000000000000))) +
      6 * ((360059771 / 250000000000000000)) * ((69232399 / 200000000000000000)) * (126 / 100) + 8 * ((69232399 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13007 165) (d.f1 13007 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13007 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13007 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13007 165) (d.f1 13007 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13007 165) (d.w1 13007 165) (d.w2 13007 165)
  have hwexpr0 : 0 ≤ d.w0 13007 165 + d.w1 13007 165 * √(π / 2) +
      2 * d.w2 13007 165 + energyR16 13007 *
      radiusPolynomialRoot16 (d.w0 13007 165) (d.w1 13007 165) (d.w2 13007 165) := by
    positivity
  constructor
  · change (13007 : ℝ) ^ 8 * (mA 13007 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13007 165) (d.f1 13007 165) d.f2 + locationR16 13007 *
        radiusPolynomialRoot16 (d.f0 13007 165) (d.f1 13007 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13007 : ℝ) ^ 8 * (mA 13007 : ℝ) ^ 8 *
        ((((4317044657 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4317044657 / 1000000000000000000)) * ((360059771 / 250000000000000000)) * (126 / 100) +
          2 * (((360059771 / 250000000000000000)) ^ 2 + 2 * ((4317044657 / 1000000000000000000)) * ((69232399 / 200000000000000000))) +
          6 * ((360059771 / 250000000000000000)) * ((69232399 / 200000000000000000)) * (126 / 100) + 8 * ((69232399 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13007) *
          (32 * (((4317044657 / 1000000000000000000) : ℝ) + (360059771 / 250000000000000000) + (69232399 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13007 : ℝ) ^ 16 *
      (d.w0 13007 165 + d.w1 13007 165 * √(π / 2) + 2 * d.w2 13007 165 +
        energyR16 13007 * radiusPolynomialRoot16 (d.w0 13007 165) (d.w1 13007 165)
          (d.w2 13007 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13007 : ℝ) ^ 16 *
        (((1706427363 / 100000000000000000000) : ℝ) + ((303522611 / 25000000000000000000)) * (126 / 100) + 2 * ((554497 / 125000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13007) *
          (32 * (((1706427363 / 100000000000000000000) : ℝ) + (303522611 / 25000000000000000000) + (554497 / 125000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13007

/-! A coarse bound on the actual paper statistics constant at dimension 13008. -/
namespace BstLean.Part266.Row13008
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13006 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13006 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13006 128 ≤ (13260 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13260 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13008) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13008 : ℕ))
    (by norm_num : (13008 : ℕ) ≤ 16384)
  have ht : paperTail256 13008 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13008 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13008 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13008 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13008 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13008 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13006 128 * √(2 / (13008 : ℝ)) *
      (√(13008 : ℝ) + paperT0 13008 + paperTail256 13008) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13008 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13008 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13008 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13006 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13006 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13008 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13008

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13008
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13008 (61 / 100) 165 (17 / (100 * 13008)) (26 / (10 * 13008)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13008 (61 / 100) 165 (17 / (100 * 13008)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (88698241 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1363749113 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4220815639 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13008 / 13008 * (61 / 100)) ^ 4 * inverseRadius8 (13008 - 1) /
            envelopeGap 13008 (61 / 100) 165 (17 / (100 * 13008)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13008

namespace BstLean.Part266.Row13008
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13008 165 ≤ (269763443 / 62500000000000000)
  f1 : (tableEnvelope C).f1 13008 165 ≤ (179995289 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (346095469 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13008 165 ≤ (213254231 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 13008 165 ≤ (60690523 / 5000000000000000000)
  w2 : (tableEnvelope C).w2 13008 165 ≤ (221747647 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (88698241 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (88698241 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1363749113 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4220815639 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((361509 / 100000000) : ℝ) ≤ √(17 / (100 * 13008) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13008) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (131620193 / 62500000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4616121737 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13008) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13008) ≤ (21743751 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13008) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13008 * (165 : ℝ) ^ 2 + 26 / (10 * 13008) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13008) : ℝ)) (tA 13008 * 165 ^ 2 + 26 / (10 * 13008)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((361509 / 100000000))) * ((88698241 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((361509 / 100000000)) ^ 3) * ((1363749113 / 1000000000000000000000000))) + ((4220815639 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((361509 / 100000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13008) : ℝ)) d.D d.V d.P (√(tA 13008) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((361509 / 100000000)) ^ 2 * (((131620193 / 62500000000000)) * ((4616121737 / 125000000000000000)))) + ((4220815639 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13008) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((361509 / 100000000)) * ((88698241 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13008) : ℝ)) (tA 13008 * 165 ^ 2 + 26 / (10 * 13008)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((88698241 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((361509 / 100000000)) ^ 2) * ((1363749113 / 1000000000000000000000000)) + ((4220815639 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13008) : ℝ)) (√(26 / (10 * 13008) : ℝ)) d.D d.V d.P (√(tA 13008) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((361509 / 100000000)) * (((131620193 / 62500000000000)) * ((4616121737 / 125000000000000000))) + ((4220815639 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13008) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((88698241 / 20000000000000000000) : ℝ) + ((4220815639 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13008

namespace BstLean.Part266.Row13008
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13008 165 ∧
    0 ≤ (tableEnvelope C).f1 13008 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13008 165 ∧
    0 ≤ (tableEnvelope C).w1 13008 165 ∧ 0 ≤ (tableEnvelope C).w2 13008 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13008 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13008 165 ∧ 0 ≤ d.f1 13008 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13008 165 ∧ 0 ≤ d.w1 13008 165 ∧ 0 ≤ d.w2 13008 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13008 ≤ 2 * (228 / 100 : ℝ) / 13008 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13008 ≤ 2 * (370 / 100 : ℝ) / 13008 := by
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
    (completeRAData (tableEnvelope C) 13008 165).locationBound 13008 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13008 165).energyBound 13008 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13008 165) (d.f1 13008 165) d.f2 ≤
      32 * (((269763443 / 62500000000000000) : ℝ) + (179995289 / 125000000000000000) + (346095469 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13008 165) (d.w1 13008 165)
      (d.w2 13008 165) ≤
      32 * (((213254231 / 12500000000000000000) : ℝ) + (60690523 / 5000000000000000000) + (221747647 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13008 165) (d.f1 13008 165) d.f2 ≤
      ((269763443 / 62500000000000000) : ℝ) ^ 2 + 2 * ((269763443 / 62500000000000000)) * ((179995289 / 125000000000000000)) * (126 / 100) +
      2 * (((179995289 / 125000000000000000)) ^ 2 + 2 * ((269763443 / 62500000000000000)) * ((346095469 / 1000000000000000000))) +
      6 * ((179995289 / 125000000000000000)) * ((346095469 / 1000000000000000000)) * (126 / 100) + 8 * ((346095469 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13008 165) (d.f1 13008 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13008 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13008 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13008 165) (d.f1 13008 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13008 165) (d.w1 13008 165) (d.w2 13008 165)
  have hwexpr0 : 0 ≤ d.w0 13008 165 + d.w1 13008 165 * √(π / 2) +
      2 * d.w2 13008 165 + energyR16 13008 *
      radiusPolynomialRoot16 (d.w0 13008 165) (d.w1 13008 165) (d.w2 13008 165) := by
    positivity
  constructor
  · change (13008 : ℝ) ^ 8 * (mA 13008 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13008 165) (d.f1 13008 165) d.f2 + locationR16 13008 *
        radiusPolynomialRoot16 (d.f0 13008 165) (d.f1 13008 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13008 : ℝ) ^ 8 * (mA 13008 : ℝ) ^ 8 *
        ((((269763443 / 62500000000000000) : ℝ) ^ 2 + 2 * ((269763443 / 62500000000000000)) * ((179995289 / 125000000000000000)) * (126 / 100) +
          2 * (((179995289 / 125000000000000000)) ^ 2 + 2 * ((269763443 / 62500000000000000)) * ((346095469 / 1000000000000000000))) +
          6 * ((179995289 / 125000000000000000)) * ((346095469 / 1000000000000000000)) * (126 / 100) + 8 * ((346095469 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13008) *
          (32 * (((269763443 / 62500000000000000) : ℝ) + (179995289 / 125000000000000000) + (346095469 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13008 : ℝ) ^ 16 *
      (d.w0 13008 165 + d.w1 13008 165 * √(π / 2) + 2 * d.w2 13008 165 +
        energyR16 13008 * radiusPolynomialRoot16 (d.w0 13008 165) (d.w1 13008 165)
          (d.w2 13008 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13008 : ℝ) ^ 16 *
        (((213254231 / 12500000000000000000) : ℝ) + ((60690523 / 5000000000000000000)) * (126 / 100) + 2 * ((221747647 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13008) *
          (32 * (((213254231 / 12500000000000000000) : ℝ) + (60690523 / 5000000000000000000) + (221747647 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13008

/-! A coarse bound on the actual paper statistics constant at dimension 13009. -/
namespace BstLean.Part266.Row13009
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13007 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13007 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13007 128 ≤ (13261 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13261 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13009) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13009 : ℕ))
    (by norm_num : (13009 : ℕ) ≤ 16384)
  have ht : paperTail256 13009 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13009 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13009 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13009 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13009 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13009 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13007 128 * √(2 / (13009 : ℝ)) *
      (√(13009 : ℝ) + paperT0 13009 + paperTail256 13009) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13009 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13009 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13009 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13007 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13007 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13009 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13009

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13009
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13009 (61 / 100) 165 (17 / (100 * 13009)) (26 / (10 * 13009)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13009 (61 / 100) 165 (17 / (100 * 13009)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (88677787 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (68166491 / 50000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4218196033 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13009 / 13009 * (61 / 100)) ^ 4 * inverseRadius8 (13009 - 1) /
            envelopeGap 13009 (61 / 100) 165 (17 / (100 * 13009)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13009

namespace BstLean.Part266.Row13009
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13009 165 ≤ (863077159 / 200000000000000000)
  f1 : (tableEnvelope C).f1 13009 165 ≤ (359921407 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (346028963 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13009 165 ≤ (1705640467 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13009 165 ≤ (1213530569 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13009 165 ≤ (221696511 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (88677787 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (88677787 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (68166491 / 50000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4218196033 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3614951 / 1000000000) : ℝ) ≤ √(17 / (100 * 13009) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13009) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2105680259 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36923296441 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13009) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13009) ≤ (54355199 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13009) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13009 * (165 : ℝ) ^ 2 + 26 / (10 * 13009) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13009) : ℝ)) (tA 13009 * 165 ^ 2 + 26 / (10 * 13009)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3614951 / 1000000000))) * ((88677787 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3614951 / 1000000000)) ^ 3) * ((68166491 / 50000000000000000000000))) + ((4218196033 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3614951 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13009) : ℝ)) d.D d.V d.P (√(tA 13009) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3614951 / 1000000000)) ^ 2 * (((2105680259 / 1000000000000000)) * ((36923296441 / 1000000000000000000)))) + ((4218196033 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13009) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3614951 / 1000000000)) * ((88677787 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13009) : ℝ)) (tA 13009 * 165 ^ 2 + 26 / (10 * 13009)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((88677787 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3614951 / 1000000000)) ^ 2) * ((68166491 / 50000000000000000000000)) + ((4218196033 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13009) : ℝ)) (√(26 / (10 * 13009) : ℝ)) d.D d.V d.P (√(tA 13009) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3614951 / 1000000000)) * (((2105680259 / 1000000000000000)) * ((36923296441 / 1000000000000000000))) + ((4218196033 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13009) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((88677787 / 20000000000000000000) : ℝ) + ((4218196033 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13009

namespace BstLean.Part266.Row13009
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13009 165 ∧
    0 ≤ (tableEnvelope C).f1 13009 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13009 165 ∧
    0 ≤ (tableEnvelope C).w1 13009 165 ∧ 0 ≤ (tableEnvelope C).w2 13009 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13009 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13009 165 ∧ 0 ≤ d.f1 13009 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13009 165 ∧ 0 ≤ d.w1 13009 165 ∧ 0 ≤ d.w2 13009 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13009 ≤ 2 * (228 / 100 : ℝ) / 13009 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13009 ≤ 2 * (370 / 100 : ℝ) / 13009 := by
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
    (completeRAData (tableEnvelope C) 13009 165).locationBound 13009 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13009 165).energyBound 13009 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13009 165) (d.f1 13009 165) d.f2 ≤
      32 * (((863077159 / 200000000000000000) : ℝ) + (359921407 / 250000000000000000) + (346028963 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13009 165) (d.w1 13009 165)
      (d.w2 13009 165) ≤
      32 * (((1705640467 / 100000000000000000000) : ℝ) + (1213530569 / 100000000000000000000) + (221696511 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13009 165) (d.f1 13009 165) d.f2 ≤
      ((863077159 / 200000000000000000) : ℝ) ^ 2 + 2 * ((863077159 / 200000000000000000)) * ((359921407 / 250000000000000000)) * (126 / 100) +
      2 * (((359921407 / 250000000000000000)) ^ 2 + 2 * ((863077159 / 200000000000000000)) * ((346028963 / 1000000000000000000))) +
      6 * ((359921407 / 250000000000000000)) * ((346028963 / 1000000000000000000)) * (126 / 100) + 8 * ((346028963 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13009 165) (d.f1 13009 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13009 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13009 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13009 165) (d.f1 13009 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13009 165) (d.w1 13009 165) (d.w2 13009 165)
  have hwexpr0 : 0 ≤ d.w0 13009 165 + d.w1 13009 165 * √(π / 2) +
      2 * d.w2 13009 165 + energyR16 13009 *
      radiusPolynomialRoot16 (d.w0 13009 165) (d.w1 13009 165) (d.w2 13009 165) := by
    positivity
  constructor
  · change (13009 : ℝ) ^ 8 * (mA 13009 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13009 165) (d.f1 13009 165) d.f2 + locationR16 13009 *
        radiusPolynomialRoot16 (d.f0 13009 165) (d.f1 13009 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13009 : ℝ) ^ 8 * (mA 13009 : ℝ) ^ 8 *
        ((((863077159 / 200000000000000000) : ℝ) ^ 2 + 2 * ((863077159 / 200000000000000000)) * ((359921407 / 250000000000000000)) * (126 / 100) +
          2 * (((359921407 / 250000000000000000)) ^ 2 + 2 * ((863077159 / 200000000000000000)) * ((346028963 / 1000000000000000000))) +
          6 * ((359921407 / 250000000000000000)) * ((346028963 / 1000000000000000000)) * (126 / 100) + 8 * ((346028963 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13009) *
          (32 * (((863077159 / 200000000000000000) : ℝ) + (359921407 / 250000000000000000) + (346028963 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13009 : ℝ) ^ 16 *
      (d.w0 13009 165 + d.w1 13009 165 * √(π / 2) + 2 * d.w2 13009 165 +
        energyR16 13009 * radiusPolynomialRoot16 (d.w0 13009 165) (d.w1 13009 165)
          (d.w2 13009 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13009 : ℝ) ^ 16 *
        (((1705640467 / 100000000000000000000) : ℝ) + ((1213530569 / 100000000000000000000)) * (126 / 100) + 2 * ((221696511 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13009) *
          (32 * (((1705640467 / 100000000000000000000) : ℝ) + (1213530569 / 100000000000000000000) + (221696511 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13009

/-! A coarse bound on the actual paper statistics constant at dimension 13010. -/
namespace BstLean.Part266.Row13010
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13008 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13008 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13008 128 ≤ (13262 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13262 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13010) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13010 : ℕ))
    (by norm_num : (13010 : ℕ) ≤ 16384)
  have ht : paperTail256 13010 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13010 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13010 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13010 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13010 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13010 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13008 128 * √(2 / (13010 : ℝ)) *
      (√(13010 : ℝ) + paperT0 13010 + paperTail256 13010) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13010 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13010 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13010 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13008 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13008 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13010 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13010

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13010
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13010 (61 / 100) 165 (17 / (100 * 13010)) (26 / (10 * 13010)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13010 (61 / 100) 165 (17 / (100 * 13010)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (88657339 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1362910689 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2107789129 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13010 / 13010 * (61 / 100)) ^ 4 * inverseRadius8 (13010 - 1) /
            envelopeGap 13010 (61 / 100) 165 (17 / (100 * 13010)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13010

namespace BstLean.Part266.Row13010
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13010 165 ≤ (4314556781 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13010 165 ≤ (143940903 / 100000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (86490619 / 250000000000000000)
  w0 : (tableEnvelope C).w0 13010 165 ≤ (106577951 / 6250000000000000000)
  w1 : (tableEnvelope C).w1 13010 165 ≤ (1213250767 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13010 165 ≤ (443290779 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (88657339 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (88657339 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1362910689 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2107789129 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((903703 / 250000000) : ℝ) ≤ √(17 / (100 * 13010) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13010) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2105437473 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18458810153 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13010) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13010) ≤ (54351021 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13010) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13010 * (165 : ℝ) ^ 2 + 26 / (10 * 13010) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13010) : ℝ)) (tA 13010 * 165 ^ 2 + 26 / (10 * 13010)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((903703 / 250000000))) * ((88657339 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((903703 / 250000000)) ^ 3) * ((1362910689 / 1000000000000000000000000))) + ((2107789129 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((903703 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13010) : ℝ)) d.D d.V d.P (√(tA 13010) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((903703 / 250000000)) ^ 2 * (((2105437473 / 1000000000000000)) * ((18458810153 / 500000000000000000)))) + ((2107789129 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13010) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((903703 / 250000000)) * ((88657339 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13010) : ℝ)) (tA 13010 * 165 ^ 2 + 26 / (10 * 13010)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((88657339 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((903703 / 250000000)) ^ 2) * ((1362910689 / 1000000000000000000000000)) + ((2107789129 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13010) : ℝ)) (√(26 / (10 * 13010) : ℝ)) d.D d.V d.P (√(tA 13010) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((903703 / 250000000)) * (((2105437473 / 1000000000000000)) * ((18458810153 / 500000000000000000))) + ((2107789129 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13010) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((88657339 / 20000000000000000000) : ℝ) + ((2107789129 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13010

namespace BstLean.Part266.Row13010
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13010 165 ∧
    0 ≤ (tableEnvelope C).f1 13010 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13010 165 ∧
    0 ≤ (tableEnvelope C).w1 13010 165 ∧ 0 ≤ (tableEnvelope C).w2 13010 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13010 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13010 165 ∧ 0 ≤ d.f1 13010 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13010 165 ∧ 0 ≤ d.w1 13010 165 ∧ 0 ≤ d.w2 13010 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13010 ≤ 2 * (228 / 100 : ℝ) / 13010 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13010 ≤ 2 * (370 / 100 : ℝ) / 13010 := by
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
    (completeRAData (tableEnvelope C) 13010 165).locationBound 13010 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13010 165).energyBound 13010 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13010 165) (d.f1 13010 165) d.f2 ≤
      32 * (((4314556781 / 1000000000000000000) : ℝ) + (143940903 / 100000000000000000) + (86490619 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13010 165) (d.w1 13010 165)
      (d.w2 13010 165) ≤
      32 * (((106577951 / 6250000000000000000) : ℝ) + (1213250767 / 100000000000000000000) + (443290779 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13010 165) (d.f1 13010 165) d.f2 ≤
      ((4314556781 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4314556781 / 1000000000000000000)) * ((143940903 / 100000000000000000)) * (126 / 100) +
      2 * (((143940903 / 100000000000000000)) ^ 2 + 2 * ((4314556781 / 1000000000000000000)) * ((86490619 / 250000000000000000))) +
      6 * ((143940903 / 100000000000000000)) * ((86490619 / 250000000000000000)) * (126 / 100) + 8 * ((86490619 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13010 165) (d.f1 13010 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13010 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13010 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13010 165) (d.f1 13010 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13010 165) (d.w1 13010 165) (d.w2 13010 165)
  have hwexpr0 : 0 ≤ d.w0 13010 165 + d.w1 13010 165 * √(π / 2) +
      2 * d.w2 13010 165 + energyR16 13010 *
      radiusPolynomialRoot16 (d.w0 13010 165) (d.w1 13010 165) (d.w2 13010 165) := by
    positivity
  constructor
  · change (13010 : ℝ) ^ 8 * (mA 13010 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13010 165) (d.f1 13010 165) d.f2 + locationR16 13010 *
        radiusPolynomialRoot16 (d.f0 13010 165) (d.f1 13010 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13010 : ℝ) ^ 8 * (mA 13010 : ℝ) ^ 8 *
        ((((4314556781 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4314556781 / 1000000000000000000)) * ((143940903 / 100000000000000000)) * (126 / 100) +
          2 * (((143940903 / 100000000000000000)) ^ 2 + 2 * ((4314556781 / 1000000000000000000)) * ((86490619 / 250000000000000000))) +
          6 * ((143940903 / 100000000000000000)) * ((86490619 / 250000000000000000)) * (126 / 100) + 8 * ((86490619 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13010) *
          (32 * (((4314556781 / 1000000000000000000) : ℝ) + (143940903 / 100000000000000000) + (86490619 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13010 : ℝ) ^ 16 *
      (d.w0 13010 165 + d.w1 13010 165 * √(π / 2) + 2 * d.w2 13010 165 +
        energyR16 13010 * radiusPolynomialRoot16 (d.w0 13010 165) (d.w1 13010 165)
          (d.w2 13010 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13010 : ℝ) ^ 16 *
        (((106577951 / 6250000000000000000) : ℝ) + ((1213250767 / 100000000000000000000)) * (126 / 100) + 2 * ((443290779 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13010) *
          (32 * (((106577951 / 6250000000000000000) : ℝ) + (1213250767 / 100000000000000000000) + (443290779 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13010

/-! A coarse bound on the actual paper statistics constant at dimension 13011. -/
namespace BstLean.Part266.Row13011
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13009 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13009 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13009 128 ≤ (13263 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13263 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13011) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13011 : ℕ))
    (by norm_num : (13011 : ℕ) ≤ 16384)
  have ht : paperTail256 13011 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13011 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13011 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13011 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13011 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13011 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13009 128 * √(2 / (13011 : ℝ)) *
      (√(13011 : ℝ) + paperT0 13011 + paperTail256 13011) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13011 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13011 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13011 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13009 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13009 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13011 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13011

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13011
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13011 (61 / 100) 165 (17 / (100 * 13011)) (26 / (10 * 13011)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13011 (61 / 100) 165 (17 / (100 * 13011)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (55398061 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (681245859 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (526620289 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13011 / 13011 * (61 / 100)) ^ 4 * inverseRadius8 (13011 - 1) /
            envelopeGap 13011 (61 / 100) 165 (17 / (100 * 13011)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13011

namespace BstLean.Part266.Row13011
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13011 165 ≤ (1078432011 / 250000000000000000)
  f1 : (tableEnvelope C).f1 13011 165 ≤ (1439132521 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (34589601 / 100000000000000000)
  w0 : (tableEnvelope C).w0 13011 165 ≤ (1704854099 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13011 165 ≤ (606485529 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13011 165 ≤ (44318857 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (55398061 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (55398061 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (681245859 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (526620289 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3614673 / 1000000000) : ℝ) ≤ √(17 / (100 * 13011) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13011) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2105194737 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7382389093 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13011) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13011) ≤ (13586711 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13011) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13011 * (165 : ℝ) ^ 2 + 26 / (10 * 13011) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13011) : ℝ)) (tA 13011 * 165 ^ 2 + 26 / (10 * 13011)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3614673 / 1000000000))) * ((55398061 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3614673 / 1000000000)) ^ 3) * ((681245859 / 500000000000000000000000))) + ((526620289 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3614673 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13011) : ℝ)) d.D d.V d.P (√(tA 13011) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3614673 / 1000000000)) ^ 2 * (((2105194737 / 1000000000000000)) * ((7382389093 / 200000000000000000)))) + ((526620289 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13011) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3614673 / 1000000000)) * ((55398061 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13011) : ℝ)) (tA 13011 * 165 ^ 2 + 26 / (10 * 13011)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((55398061 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3614673 / 1000000000)) ^ 2) * ((681245859 / 500000000000000000000000)) + ((526620289 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13011) : ℝ)) (√(26 / (10 * 13011) : ℝ)) d.D d.V d.P (√(tA 13011) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3614673 / 1000000000)) * (((2105194737 / 1000000000000000)) * ((7382389093 / 200000000000000000))) + ((526620289 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13011) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((55398061 / 12500000000000000000) : ℝ) + ((526620289 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13011

namespace BstLean.Part266.Row13011
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13011 165 ∧
    0 ≤ (tableEnvelope C).f1 13011 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13011 165 ∧
    0 ≤ (tableEnvelope C).w1 13011 165 ∧ 0 ≤ (tableEnvelope C).w2 13011 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13011 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13011 165 ∧ 0 ≤ d.f1 13011 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13011 165 ∧ 0 ≤ d.w1 13011 165 ∧ 0 ≤ d.w2 13011 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13011 ≤ 2 * (228 / 100 : ℝ) / 13011 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13011 ≤ 2 * (370 / 100 : ℝ) / 13011 := by
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
    (completeRAData (tableEnvelope C) 13011 165).locationBound 13011 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13011 165).energyBound 13011 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13011 165) (d.f1 13011 165) d.f2 ≤
      32 * (((1078432011 / 250000000000000000) : ℝ) + (1439132521 / 1000000000000000000) + (34589601 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13011 165) (d.w1 13011 165)
      (d.w2 13011 165) ≤
      32 * (((1704854099 / 100000000000000000000) : ℝ) + (606485529 / 50000000000000000000) + (44318857 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13011 165) (d.f1 13011 165) d.f2 ≤
      ((1078432011 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1078432011 / 250000000000000000)) * ((1439132521 / 1000000000000000000)) * (126 / 100) +
      2 * (((1439132521 / 1000000000000000000)) ^ 2 + 2 * ((1078432011 / 250000000000000000)) * ((34589601 / 100000000000000000))) +
      6 * ((1439132521 / 1000000000000000000)) * ((34589601 / 100000000000000000)) * (126 / 100) + 8 * ((34589601 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13011 165) (d.f1 13011 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13011 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13011 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13011 165) (d.f1 13011 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13011 165) (d.w1 13011 165) (d.w2 13011 165)
  have hwexpr0 : 0 ≤ d.w0 13011 165 + d.w1 13011 165 * √(π / 2) +
      2 * d.w2 13011 165 + energyR16 13011 *
      radiusPolynomialRoot16 (d.w0 13011 165) (d.w1 13011 165) (d.w2 13011 165) := by
    positivity
  constructor
  · change (13011 : ℝ) ^ 8 * (mA 13011 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13011 165) (d.f1 13011 165) d.f2 + locationR16 13011 *
        radiusPolynomialRoot16 (d.f0 13011 165) (d.f1 13011 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13011 : ℝ) ^ 8 * (mA 13011 : ℝ) ^ 8 *
        ((((1078432011 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1078432011 / 250000000000000000)) * ((1439132521 / 1000000000000000000)) * (126 / 100) +
          2 * (((1439132521 / 1000000000000000000)) ^ 2 + 2 * ((1078432011 / 250000000000000000)) * ((34589601 / 100000000000000000))) +
          6 * ((1439132521 / 1000000000000000000)) * ((34589601 / 100000000000000000)) * (126 / 100) + 8 * ((34589601 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13011) *
          (32 * (((1078432011 / 250000000000000000) : ℝ) + (1439132521 / 1000000000000000000) + (34589601 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13011 : ℝ) ^ 16 *
      (d.w0 13011 165 + d.w1 13011 165 * √(π / 2) + 2 * d.w2 13011 165 +
        energyR16 13011 * radiusPolynomialRoot16 (d.w0 13011 165) (d.w1 13011 165)
          (d.w2 13011 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13011 : ℝ) ^ 16 *
        (((1704854099 / 100000000000000000000) : ℝ) + ((606485529 / 50000000000000000000)) * (126 / 100) + 2 * ((44318857 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13011) *
          (32 * (((1704854099 / 100000000000000000000) : ℝ) + (606485529 / 50000000000000000000) + (44318857 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13011

/-! A coarse bound on the actual paper statistics constant at dimension 13012. -/
namespace BstLean.Part266.Row13012
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13010 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13010 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13010 128 ≤ (13264 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13264 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13012) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13012 : ℕ))
    (by norm_num : (13012 : ℕ) ≤ 16384)
  have ht : paperTail256 13012 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13012 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13012 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13012 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13012 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13012 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13010 128 * √(2 / (13012 : ℝ)) *
      (√(13012 : ℝ) + paperT0 13012 + paperTail256 13012) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13012 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13012 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13012 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13010 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13010 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13012 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13012

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13012
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13012 (61 / 100) 165 (17 / (100 * 13012)) (26 / (10 * 13012)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13012 (61 / 100) 165 (17 / (100 * 13012)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (443082311 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1362072909 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4210348193 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13012 / 13012 * (61 / 100)) ^ 4 * inverseRadius8 (13012 - 1) /
            envelopeGap 13012 (61 / 100) 165 (17 / (100 * 13012)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13012

namespace BstLean.Part266.Row13012
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13012 165 ≤ (4312899587 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13012 165 ≤ (1438856097 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (345829561 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13012 165 ≤ (1704461113 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13012 165 ≤ (15158643 / 1250000000000000000)
  w2 : (tableEnvelope C).w2 13012 165 ≤ (44308639 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (443082311 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (443082311 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1362072909 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4210348193 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1807267 / 500000000) : ℝ) ≤ √(17 / (100 * 13012) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13012) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (420990409 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36906271947 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13012) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13012) ≤ (54342667 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13012) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13012 * (165 : ℝ) ^ 2 + 26 / (10 * 13012) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13012) : ℝ)) (tA 13012 * 165 ^ 2 + 26 / (10 * 13012)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1807267 / 500000000))) * ((443082311 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1807267 / 500000000)) ^ 3) * ((1362072909 / 1000000000000000000000000))) + ((4210348193 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1807267 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13012) : ℝ)) d.D d.V d.P (√(tA 13012) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1807267 / 500000000)) ^ 2 * (((420990409 / 200000000000000)) * ((36906271947 / 1000000000000000000)))) + ((4210348193 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13012) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1807267 / 500000000)) * ((443082311 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13012) : ℝ)) (tA 13012 * 165 ^ 2 + 26 / (10 * 13012)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((443082311 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1807267 / 500000000)) ^ 2) * ((1362072909 / 1000000000000000000000000)) + ((4210348193 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13012) : ℝ)) (√(26 / (10 * 13012) : ℝ)) d.D d.V d.P (√(tA 13012) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1807267 / 500000000)) * (((420990409 / 200000000000000)) * ((36906271947 / 1000000000000000000))) + ((4210348193 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13012) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((443082311 / 100000000000000000000) : ℝ) + ((4210348193 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13012

namespace BstLean.Part266.Row13012
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13012 165 ∧
    0 ≤ (tableEnvelope C).f1 13012 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13012 165 ∧
    0 ≤ (tableEnvelope C).w1 13012 165 ∧ 0 ≤ (tableEnvelope C).w2 13012 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13012 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13012 165 ∧ 0 ≤ d.f1 13012 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13012 165 ∧ 0 ≤ d.w1 13012 165 ∧ 0 ≤ d.w2 13012 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13012 ≤ 2 * (228 / 100 : ℝ) / 13012 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13012 ≤ 2 * (370 / 100 : ℝ) / 13012 := by
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
    (completeRAData (tableEnvelope C) 13012 165).locationBound 13012 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13012 165).energyBound 13012 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13012 165) (d.f1 13012 165) d.f2 ≤
      32 * (((4312899587 / 1000000000000000000) : ℝ) + (1438856097 / 1000000000000000000) + (345829561 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13012 165) (d.w1 13012 165)
      (d.w2 13012 165) ≤
      32 * (((1704461113 / 100000000000000000000) : ℝ) + (15158643 / 1250000000000000000) + (44308639 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13012 165) (d.f1 13012 165) d.f2 ≤
      ((4312899587 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4312899587 / 1000000000000000000)) * ((1438856097 / 1000000000000000000)) * (126 / 100) +
      2 * (((1438856097 / 1000000000000000000)) ^ 2 + 2 * ((4312899587 / 1000000000000000000)) * ((345829561 / 1000000000000000000))) +
      6 * ((1438856097 / 1000000000000000000)) * ((345829561 / 1000000000000000000)) * (126 / 100) + 8 * ((345829561 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13012 165) (d.f1 13012 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13012 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13012 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13012 165) (d.f1 13012 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13012 165) (d.w1 13012 165) (d.w2 13012 165)
  have hwexpr0 : 0 ≤ d.w0 13012 165 + d.w1 13012 165 * √(π / 2) +
      2 * d.w2 13012 165 + energyR16 13012 *
      radiusPolynomialRoot16 (d.w0 13012 165) (d.w1 13012 165) (d.w2 13012 165) := by
    positivity
  constructor
  · change (13012 : ℝ) ^ 8 * (mA 13012 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13012 165) (d.f1 13012 165) d.f2 + locationR16 13012 *
        radiusPolynomialRoot16 (d.f0 13012 165) (d.f1 13012 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13012 : ℝ) ^ 8 * (mA 13012 : ℝ) ^ 8 *
        ((((4312899587 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4312899587 / 1000000000000000000)) * ((1438856097 / 1000000000000000000)) * (126 / 100) +
          2 * (((1438856097 / 1000000000000000000)) ^ 2 + 2 * ((4312899587 / 1000000000000000000)) * ((345829561 / 1000000000000000000))) +
          6 * ((1438856097 / 1000000000000000000)) * ((345829561 / 1000000000000000000)) * (126 / 100) + 8 * ((345829561 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13012) *
          (32 * (((4312899587 / 1000000000000000000) : ℝ) + (1438856097 / 1000000000000000000) + (345829561 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13012 : ℝ) ^ 16 *
      (d.w0 13012 165 + d.w1 13012 165 * √(π / 2) + 2 * d.w2 13012 165 +
        energyR16 13012 * radiusPolynomialRoot16 (d.w0 13012 165) (d.w1 13012 165)
          (d.w2 13012 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13012 : ℝ) ^ 16 *
        (((1704461113 / 100000000000000000000) : ℝ) + ((15158643 / 1250000000000000000)) * (126 / 100) + 2 * ((44308639 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13012) *
          (32 * (((1704461113 / 100000000000000000000) : ℝ) + (15158643 / 1250000000000000000) + (44308639 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13012

/-! A coarse bound on the actual paper statistics constant at dimension 13013. -/
namespace BstLean.Part266.Row13013
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13011 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13011 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13011 128 ≤ (13265 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13265 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13013) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13013 : ℕ))
    (by norm_num : (13013 : ℕ) ≤ 16384)
  have ht : paperTail256 13013 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13013 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13013 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13013 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13013 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13013 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13011 128 * √(2 / (13013 : ℝ)) *
      (√(13013 : ℝ) + paperT0 13013 + paperTail256 13013) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13013 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13013 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13013 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13011 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13011 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13013 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13013

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13013
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13013 (61 / 100) 165 (17 / (100 * 13013)) (26 / (10 * 13013)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13013 (61 / 100) 165 (17 / (100 * 13013)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (221490083 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (68082713 / 50000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2103867951 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13013 / 13013 * (61 / 100)) ^ 4 * inverseRadius8 (13013 - 1) /
            envelopeGap 13013 (61 / 100) 165 (17 / (100 * 13013)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13013

namespace BstLean.Part266.Row13013
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13013 165 ≤ (4312067961 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13013 165 ≤ (287715793 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (345763037 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13013 165 ≤ (1704067561 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13013 165 ≤ (606205789 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13013 165 ≤ (221492121 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (221490083 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (221490083 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (68082713 / 50000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2103867951 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((903599 / 250000000) : ℝ) ≤ √(17 / (100 * 13013) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13013) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2104709401 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1476023989 / 40000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13013) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13013) ≤ (54338491 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13013) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13013 * (165 : ℝ) ^ 2 + 26 / (10 * 13013) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13013) : ℝ)) (tA 13013 * 165 ^ 2 + 26 / (10 * 13013)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((903599 / 250000000))) * ((221490083 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((903599 / 250000000)) ^ 3) * ((68082713 / 50000000000000000000000))) + ((2103867951 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((903599 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13013) : ℝ)) d.D d.V d.P (√(tA 13013) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((903599 / 250000000)) ^ 2 * (((2104709401 / 1000000000000000)) * ((1476023989 / 40000000000000000)))) + ((2103867951 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13013) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((903599 / 250000000)) * ((221490083 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13013) : ℝ)) (tA 13013 * 165 ^ 2 + 26 / (10 * 13013)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((221490083 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((903599 / 250000000)) ^ 2) * ((68082713 / 50000000000000000000000)) + ((2103867951 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13013) : ℝ)) (√(26 / (10 * 13013) : ℝ)) d.D d.V d.P (√(tA 13013) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((903599 / 250000000)) * (((2104709401 / 1000000000000000)) * ((1476023989 / 40000000000000000))) + ((2103867951 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13013) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((221490083 / 50000000000000000000) : ℝ) + ((2103867951 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13013

namespace BstLean.Part266.Row13013
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13013 165 ∧
    0 ≤ (tableEnvelope C).f1 13013 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13013 165 ∧
    0 ≤ (tableEnvelope C).w1 13013 165 ∧ 0 ≤ (tableEnvelope C).w2 13013 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13013 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13013 165 ∧ 0 ≤ d.f1 13013 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13013 165 ∧ 0 ≤ d.w1 13013 165 ∧ 0 ≤ d.w2 13013 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13013 ≤ 2 * (228 / 100 : ℝ) / 13013 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13013 ≤ 2 * (370 / 100 : ℝ) / 13013 := by
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
    (completeRAData (tableEnvelope C) 13013 165).locationBound 13013 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13013 165).energyBound 13013 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13013 165) (d.f1 13013 165) d.f2 ≤
      32 * (((4312067961 / 1000000000000000000) : ℝ) + (287715793 / 200000000000000000) + (345763037 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13013 165) (d.w1 13013 165)
      (d.w2 13013 165) ≤
      32 * (((1704067561 / 100000000000000000000) : ℝ) + (606205789 / 50000000000000000000) + (221492121 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13013 165) (d.f1 13013 165) d.f2 ≤
      ((4312067961 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4312067961 / 1000000000000000000)) * ((287715793 / 200000000000000000)) * (126 / 100) +
      2 * (((287715793 / 200000000000000000)) ^ 2 + 2 * ((4312067961 / 1000000000000000000)) * ((345763037 / 1000000000000000000))) +
      6 * ((287715793 / 200000000000000000)) * ((345763037 / 1000000000000000000)) * (126 / 100) + 8 * ((345763037 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13013 165) (d.f1 13013 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13013 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13013 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13013 165) (d.f1 13013 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13013 165) (d.w1 13013 165) (d.w2 13013 165)
  have hwexpr0 : 0 ≤ d.w0 13013 165 + d.w1 13013 165 * √(π / 2) +
      2 * d.w2 13013 165 + energyR16 13013 *
      radiusPolynomialRoot16 (d.w0 13013 165) (d.w1 13013 165) (d.w2 13013 165) := by
    positivity
  constructor
  · change (13013 : ℝ) ^ 8 * (mA 13013 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13013 165) (d.f1 13013 165) d.f2 + locationR16 13013 *
        radiusPolynomialRoot16 (d.f0 13013 165) (d.f1 13013 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13013 : ℝ) ^ 8 * (mA 13013 : ℝ) ^ 8 *
        ((((4312067961 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4312067961 / 1000000000000000000)) * ((287715793 / 200000000000000000)) * (126 / 100) +
          2 * (((287715793 / 200000000000000000)) ^ 2 + 2 * ((4312067961 / 1000000000000000000)) * ((345763037 / 1000000000000000000))) +
          6 * ((287715793 / 200000000000000000)) * ((345763037 / 1000000000000000000)) * (126 / 100) + 8 * ((345763037 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13013) *
          (32 * (((4312067961 / 1000000000000000000) : ℝ) + (287715793 / 200000000000000000) + (345763037 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13013 : ℝ) ^ 16 *
      (d.w0 13013 165 + d.w1 13013 165 * √(π / 2) + 2 * d.w2 13013 165 +
        energyR16 13013 * radiusPolynomialRoot16 (d.w0 13013 165) (d.w1 13013 165)
          (d.w2 13013 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13013 : ℝ) ^ 16 *
        (((1704067561 / 100000000000000000000) : ℝ) + ((606205789 / 50000000000000000000)) * (126 / 100) + 2 * ((221492121 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13013) *
          (32 * (((1704067561 / 100000000000000000000) : ℝ) + (606205789 / 50000000000000000000) + (221492121 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13013

/-! A coarse bound on the actual paper statistics constant at dimension 13014. -/
namespace BstLean.Part266.Row13014
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13012 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13012 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13012 128 ≤ (13266 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13266 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13014) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13014 : ℕ))
    (by norm_num : (13014 : ℕ) ≤ 16384)
  have ht : paperTail256 13014 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13014 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13014 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13014 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13014 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13014 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13012 128 * √(2 / (13014 : ℝ)) *
      (√(13014 : ℝ) + paperT0 13014 + paperTail256 13014) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13014 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13014 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13014 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13012 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13012 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13014 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13014

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13014
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13014 (61 / 100) 165 (17 / (100 * 13014)) (26 / (10 * 13014)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13014 (61 / 100) 165 (17 / (100 * 13014)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (442878053 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1361235773 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (841025087 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13014 / 13014 * (61 / 100)) ^ 4 * inverseRadius8 (13014 - 1) /
            envelopeGap 13014 (61 / 100) 165 (17 / (100 * 13014)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13014

namespace BstLean.Part266.Row13014
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13014 165 ≤ (2155620031 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13014 165 ≤ (719151359 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (345696629 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13014 165 ≤ (42591871 / 2500000000000000000)
  w1 : (tableEnvelope C).w1 13014 165 ≤ (75758259 / 6250000000000000000)
  w2 : (tableEnvelope C).w2 13014 165 ≤ (442882127 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (442878053 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (442878053 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1361235773 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (841025087 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3614257 / 1000000000) : ℝ) ≤ √(17 / (100 * 13014) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13014) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (420893361 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1475797153 / 40000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13014) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13014) ≤ (108668631 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13014) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13014 * (165 : ℝ) ^ 2 + 26 / (10 * 13014) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13014) : ℝ)) (tA 13014 * 165 ^ 2 + 26 / (10 * 13014)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3614257 / 1000000000))) * ((442878053 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3614257 / 1000000000)) ^ 3) * ((1361235773 / 1000000000000000000000000))) + ((841025087 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3614257 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13014) : ℝ)) d.D d.V d.P (√(tA 13014) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3614257 / 1000000000)) ^ 2 * (((420893361 / 200000000000000)) * ((1475797153 / 40000000000000000)))) + ((841025087 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13014) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3614257 / 1000000000)) * ((442878053 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13014) : ℝ)) (tA 13014 * 165 ^ 2 + 26 / (10 * 13014)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((442878053 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3614257 / 1000000000)) ^ 2) * ((1361235773 / 1000000000000000000000000)) + ((841025087 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13014) : ℝ)) (√(26 / (10 * 13014) : ℝ)) d.D d.V d.P (√(tA 13014) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3614257 / 1000000000)) * (((420893361 / 200000000000000)) * ((1475797153 / 40000000000000000))) + ((841025087 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13014) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((442878053 / 100000000000000000000) : ℝ) + ((841025087 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13014

namespace BstLean.Part266.Row13014
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13014 165 ∧
    0 ≤ (tableEnvelope C).f1 13014 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13014 165 ∧
    0 ≤ (tableEnvelope C).w1 13014 165 ∧ 0 ≤ (tableEnvelope C).w2 13014 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13014 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13014 165 ∧ 0 ≤ d.f1 13014 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13014 165 ∧ 0 ≤ d.w1 13014 165 ∧ 0 ≤ d.w2 13014 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13014 ≤ 2 * (228 / 100 : ℝ) / 13014 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13014 ≤ 2 * (370 / 100 : ℝ) / 13014 := by
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
    (completeRAData (tableEnvelope C) 13014 165).locationBound 13014 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13014 165).energyBound 13014 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13014 165) (d.f1 13014 165) d.f2 ≤
      32 * (((2155620031 / 500000000000000000) : ℝ) + (719151359 / 500000000000000000) + (345696629 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13014 165) (d.w1 13014 165)
      (d.w2 13014 165) ≤
      32 * (((42591871 / 2500000000000000000) : ℝ) + (75758259 / 6250000000000000000) + (442882127 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13014 165) (d.f1 13014 165) d.f2 ≤
      ((2155620031 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2155620031 / 500000000000000000)) * ((719151359 / 500000000000000000)) * (126 / 100) +
      2 * (((719151359 / 500000000000000000)) ^ 2 + 2 * ((2155620031 / 500000000000000000)) * ((345696629 / 1000000000000000000))) +
      6 * ((719151359 / 500000000000000000)) * ((345696629 / 1000000000000000000)) * (126 / 100) + 8 * ((345696629 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13014 165) (d.f1 13014 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13014 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13014 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13014 165) (d.f1 13014 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13014 165) (d.w1 13014 165) (d.w2 13014 165)
  have hwexpr0 : 0 ≤ d.w0 13014 165 + d.w1 13014 165 * √(π / 2) +
      2 * d.w2 13014 165 + energyR16 13014 *
      radiusPolynomialRoot16 (d.w0 13014 165) (d.w1 13014 165) (d.w2 13014 165) := by
    positivity
  constructor
  · change (13014 : ℝ) ^ 8 * (mA 13014 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13014 165) (d.f1 13014 165) d.f2 + locationR16 13014 *
        radiusPolynomialRoot16 (d.f0 13014 165) (d.f1 13014 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13014 : ℝ) ^ 8 * (mA 13014 : ℝ) ^ 8 *
        ((((2155620031 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2155620031 / 500000000000000000)) * ((719151359 / 500000000000000000)) * (126 / 100) +
          2 * (((719151359 / 500000000000000000)) ^ 2 + 2 * ((2155620031 / 500000000000000000)) * ((345696629 / 1000000000000000000))) +
          6 * ((719151359 / 500000000000000000)) * ((345696629 / 1000000000000000000)) * (126 / 100) + 8 * ((345696629 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13014) *
          (32 * (((2155620031 / 500000000000000000) : ℝ) + (719151359 / 500000000000000000) + (345696629 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13014 : ℝ) ^ 16 *
      (d.w0 13014 165 + d.w1 13014 165 * √(π / 2) + 2 * d.w2 13014 165 +
        energyR16 13014 * radiusPolynomialRoot16 (d.w0 13014 165) (d.w1 13014 165)
          (d.w2 13014 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13014 : ℝ) ^ 16 *
        (((42591871 / 2500000000000000000) : ℝ) + ((75758259 / 6250000000000000000)) * (126 / 100) + 2 * ((442882127 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13014) *
          (32 * (((42591871 / 2500000000000000000) : ℝ) + (75758259 / 6250000000000000000) + (442882127 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13014

/-! A coarse bound on the actual paper statistics constant at dimension 13015. -/
namespace BstLean.Part266.Row13015
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13013 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13013 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13013 128 ≤ (13267 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13267 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13015) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13015 : ℕ))
    (by norm_num : (13015 : ℕ) ≤ 16384)
  have ht : paperTail256 13015 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13015 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13015 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13015 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13015 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13015 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13013 128 * √(2 / (13015 : ℝ)) *
      (√(13015 : ℝ) + paperT0 13015 + paperTail256 13015) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13015 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13015 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13015 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13013 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13013 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13015 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13015

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13015
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13015 (61 / 100) 165 (17 / (100 * 13015)) (26 / (10 * 13015)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13015 (61 / 100) 165 (17 / (100 * 13015)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (44277597 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (680408723 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4202516793 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13015 / 13015 * (61 / 100)) ^ 4 * inverseRadius8 (13015 - 1) /
            envelopeGap 13015 (61 / 100) 165 (17 / (100 * 13015)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13015

namespace BstLean.Part266.Row13015
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13015 165 ≤ (4310412437 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13015 165 ≤ (287605311 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (172815119 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13015 165 ≤ (1703282249 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13015 165 ≤ (1211852799 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13015 165 ≤ (442780041 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (44277597 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (44277597 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (680408723 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4202516793 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1807059 / 500000000) : ℝ) ≤ √(17 / (100 * 13015) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13015) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (526056063 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36889259223 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13015) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13015) ≤ (54330141 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13015) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13015 * (165 : ℝ) ^ 2 + 26 / (10 * 13015) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13015) : ℝ)) (tA 13015 * 165 ^ 2 + 26 / (10 * 13015)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1807059 / 500000000))) * ((44277597 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1807059 / 500000000)) ^ 3) * ((680408723 / 500000000000000000000000))) + ((4202516793 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1807059 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13015) : ℝ)) d.D d.V d.P (√(tA 13015) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1807059 / 500000000)) ^ 2 * (((526056063 / 250000000000000)) * ((36889259223 / 1000000000000000000)))) + ((4202516793 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13015) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1807059 / 500000000)) * ((44277597 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13015) : ℝ)) (tA 13015 * 165 ^ 2 + 26 / (10 * 13015)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((44277597 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1807059 / 500000000)) ^ 2) * ((680408723 / 500000000000000000000000)) + ((4202516793 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13015) : ℝ)) (√(26 / (10 * 13015) : ℝ)) d.D d.V d.P (√(tA 13015) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1807059 / 500000000)) * (((526056063 / 250000000000000)) * ((36889259223 / 1000000000000000000))) + ((4202516793 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13015) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((44277597 / 10000000000000000000) : ℝ) + ((4202516793 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13015

namespace BstLean.Part266.Row13015
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13015 165 ∧
    0 ≤ (tableEnvelope C).f1 13015 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13015 165 ∧
    0 ≤ (tableEnvelope C).w1 13015 165 ∧ 0 ≤ (tableEnvelope C).w2 13015 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13015 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13015 165 ∧ 0 ≤ d.f1 13015 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13015 165 ∧ 0 ≤ d.w1 13015 165 ∧ 0 ≤ d.w2 13015 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13015 ≤ 2 * (228 / 100 : ℝ) / 13015 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13015 ≤ 2 * (370 / 100 : ℝ) / 13015 := by
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
    (completeRAData (tableEnvelope C) 13015 165).locationBound 13015 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13015 165).energyBound 13015 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13015 165) (d.f1 13015 165) d.f2 ≤
      32 * (((4310412437 / 1000000000000000000) : ℝ) + (287605311 / 200000000000000000) + (172815119 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13015 165) (d.w1 13015 165)
      (d.w2 13015 165) ≤
      32 * (((1703282249 / 100000000000000000000) : ℝ) + (1211852799 / 100000000000000000000) + (442780041 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13015 165) (d.f1 13015 165) d.f2 ≤
      ((4310412437 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4310412437 / 1000000000000000000)) * ((287605311 / 200000000000000000)) * (126 / 100) +
      2 * (((287605311 / 200000000000000000)) ^ 2 + 2 * ((4310412437 / 1000000000000000000)) * ((172815119 / 500000000000000000))) +
      6 * ((287605311 / 200000000000000000)) * ((172815119 / 500000000000000000)) * (126 / 100) + 8 * ((172815119 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13015 165) (d.f1 13015 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13015 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13015 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13015 165) (d.f1 13015 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13015 165) (d.w1 13015 165) (d.w2 13015 165)
  have hwexpr0 : 0 ≤ d.w0 13015 165 + d.w1 13015 165 * √(π / 2) +
      2 * d.w2 13015 165 + energyR16 13015 *
      radiusPolynomialRoot16 (d.w0 13015 165) (d.w1 13015 165) (d.w2 13015 165) := by
    positivity
  constructor
  · change (13015 : ℝ) ^ 8 * (mA 13015 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13015 165) (d.f1 13015 165) d.f2 + locationR16 13015 *
        radiusPolynomialRoot16 (d.f0 13015 165) (d.f1 13015 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13015 : ℝ) ^ 8 * (mA 13015 : ℝ) ^ 8 *
        ((((4310412437 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4310412437 / 1000000000000000000)) * ((287605311 / 200000000000000000)) * (126 / 100) +
          2 * (((287605311 / 200000000000000000)) ^ 2 + 2 * ((4310412437 / 1000000000000000000)) * ((172815119 / 500000000000000000))) +
          6 * ((287605311 / 200000000000000000)) * ((172815119 / 500000000000000000)) * (126 / 100) + 8 * ((172815119 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13015) *
          (32 * (((4310412437 / 1000000000000000000) : ℝ) + (287605311 / 200000000000000000) + (172815119 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13015 : ℝ) ^ 16 *
      (d.w0 13015 165 + d.w1 13015 165 * √(π / 2) + 2 * d.w2 13015 165 +
        energyR16 13015 * radiusPolynomialRoot16 (d.w0 13015 165) (d.w1 13015 165)
          (d.w2 13015 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13015 : ℝ) ^ 16 *
        (((1703282249 / 100000000000000000000) : ℝ) + ((1211852799 / 100000000000000000000)) * (126 / 100) + 2 * ((442780041 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13015) *
          (32 * (((1703282249 / 100000000000000000000) : ℝ) + (1211852799 / 100000000000000000000) + (442780041 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13015

/-! A coarse bound on the actual paper statistics constant at dimension 13016. -/
namespace BstLean.Part266.Row13016
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13014 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13014 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13014 128 ≤ (13268 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13268 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13016) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13016 : ℕ))
    (by norm_num : (13016 : ℕ) ≤ 16384)
  have ht : paperTail256 13016 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13016 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13016 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13016 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13016 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13016 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13014 128 * √(2 / (13016 : ℝ)) *
      (√(13016 : ℝ) + paperT0 13016 + paperTail256 13016) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13016 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13016 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13016 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13014 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13014 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13016 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13016

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13016
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13016 (61 / 100) 165 (17 / (100 * 13016)) (26 / (10 * 13016)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13016 (61 / 100) 165 (17 / (100 * 13016)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (442673919 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1360399279 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1049977493 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13016 / 13016 * (61 / 100)) ^ 4 * inverseRadius8 (13016 - 1) /
            envelopeGap 13016 (61 / 100) 165 (17 / (100 * 13016)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13016

namespace BstLean.Part266.Row13016
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13016 165 ≤ (67337267 / 15625000000000000)
  f1 : (tableEnvelope C).f1 13016 165 ≤ (1437750479 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (86390967 / 250000000000000000)
  w0 : (tableEnvelope C).w0 13016 165 ≤ (170288979 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 13016 165 ≤ (242314709 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 13016 165 ≤ (110669497 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (442673919 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (442673919 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1360399279 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1049977493 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3613979 / 1000000000) : ℝ) ≤ √(17 / (100 * 13016) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13016) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2103981747 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18441795459 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13016) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13016) ≤ (54325967 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13016) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13016 * (165 : ℝ) ^ 2 + 26 / (10 * 13016) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13016) : ℝ)) (tA 13016 * 165 ^ 2 + 26 / (10 * 13016)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3613979 / 1000000000))) * ((442673919 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3613979 / 1000000000)) ^ 3) * ((1360399279 / 1000000000000000000000000))) + ((1049977493 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3613979 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13016) : ℝ)) d.D d.V d.P (√(tA 13016) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3613979 / 1000000000)) ^ 2 * (((2103981747 / 1000000000000000)) * ((18441795459 / 500000000000000000)))) + ((1049977493 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13016) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3613979 / 1000000000)) * ((442673919 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13016) : ℝ)) (tA 13016 * 165 ^ 2 + 26 / (10 * 13016)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((442673919 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3613979 / 1000000000)) ^ 2) * ((1360399279 / 1000000000000000000000000)) + ((1049977493 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13016) : ℝ)) (√(26 / (10 * 13016) : ℝ)) d.D d.V d.P (√(tA 13016) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3613979 / 1000000000)) * (((2103981747 / 1000000000000000)) * ((18441795459 / 500000000000000000))) + ((1049977493 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13016) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((442673919 / 100000000000000000000) : ℝ) + ((1049977493 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13016

namespace BstLean.Part266.Row13016
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13016 165 ∧
    0 ≤ (tableEnvelope C).f1 13016 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13016 165 ∧
    0 ≤ (tableEnvelope C).w1 13016 165 ∧ 0 ≤ (tableEnvelope C).w2 13016 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13016 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13016 165 ∧ 0 ≤ d.f1 13016 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13016 165 ∧ 0 ≤ d.w1 13016 165 ∧ 0 ≤ d.w2 13016 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13016 ≤ 2 * (228 / 100 : ℝ) / 13016 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13016 ≤ 2 * (370 / 100 : ℝ) / 13016 := by
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
    (completeRAData (tableEnvelope C) 13016 165).locationBound 13016 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13016 165).energyBound 13016 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13016 165) (d.f1 13016 165) d.f2 ≤
      32 * (((67337267 / 15625000000000000) : ℝ) + (1437750479 / 1000000000000000000) + (86390967 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13016 165) (d.w1 13016 165)
      (d.w2 13016 165) ≤
      32 * (((170288979 / 10000000000000000000) : ℝ) + (242314709 / 20000000000000000000) + (110669497 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13016 165) (d.f1 13016 165) d.f2 ≤
      ((67337267 / 15625000000000000) : ℝ) ^ 2 + 2 * ((67337267 / 15625000000000000)) * ((1437750479 / 1000000000000000000)) * (126 / 100) +
      2 * (((1437750479 / 1000000000000000000)) ^ 2 + 2 * ((67337267 / 15625000000000000)) * ((86390967 / 250000000000000000))) +
      6 * ((1437750479 / 1000000000000000000)) * ((86390967 / 250000000000000000)) * (126 / 100) + 8 * ((86390967 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13016 165) (d.f1 13016 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13016 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13016 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13016 165) (d.f1 13016 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13016 165) (d.w1 13016 165) (d.w2 13016 165)
  have hwexpr0 : 0 ≤ d.w0 13016 165 + d.w1 13016 165 * √(π / 2) +
      2 * d.w2 13016 165 + energyR16 13016 *
      radiusPolynomialRoot16 (d.w0 13016 165) (d.w1 13016 165) (d.w2 13016 165) := by
    positivity
  constructor
  · change (13016 : ℝ) ^ 8 * (mA 13016 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13016 165) (d.f1 13016 165) d.f2 + locationR16 13016 *
        radiusPolynomialRoot16 (d.f0 13016 165) (d.f1 13016 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13016 : ℝ) ^ 8 * (mA 13016 : ℝ) ^ 8 *
        ((((67337267 / 15625000000000000) : ℝ) ^ 2 + 2 * ((67337267 / 15625000000000000)) * ((1437750479 / 1000000000000000000)) * (126 / 100) +
          2 * (((1437750479 / 1000000000000000000)) ^ 2 + 2 * ((67337267 / 15625000000000000)) * ((86390967 / 250000000000000000))) +
          6 * ((1437750479 / 1000000000000000000)) * ((86390967 / 250000000000000000)) * (126 / 100) + 8 * ((86390967 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13016) *
          (32 * (((67337267 / 15625000000000000) : ℝ) + (1437750479 / 1000000000000000000) + (86390967 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13016 : ℝ) ^ 16 *
      (d.w0 13016 165 + d.w1 13016 165 * √(π / 2) + 2 * d.w2 13016 165 +
        energyR16 13016 * radiusPolynomialRoot16 (d.w0 13016 165) (d.w1 13016 165)
          (d.w2 13016 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13016 : ℝ) ^ 16 *
        (((170288979 / 10000000000000000000) : ℝ) + ((242314709 / 20000000000000000000)) * (126 / 100) + 2 * ((110669497 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13016) *
          (32 * (((170288979 / 10000000000000000000) : ℝ) + (242314709 / 20000000000000000000) + (110669497 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13016

/-! A coarse bound on the actual paper statistics constant at dimension 13017. -/
namespace BstLean.Part266.Row13017
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13015 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13015 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13015 128 ≤ (13269 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13269 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13017) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13017 : ℕ))
    (by norm_num : (13017 : ℕ) ≤ 16384)
  have ht : paperTail256 13017 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13017 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13017 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13017 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13017 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13017 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13015 128 * √(2 / (13017 : ℝ)) *
      (√(13017 : ℝ) + paperT0 13017 + paperTail256 13017) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13017 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13017 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13017 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13015 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13015 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13017 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13017

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13017
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13017 (61 / 100) 165 (17 / (100 * 13017)) (26 / (10 * 13017)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13017 (61 / 100) 165 (17 / (100 * 13017)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (4425719 / 1000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (679990637 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1049326243 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13017 / 13017 * (61 / 100)) ^ 4 * inverseRadius8 (13017 - 1) /
            envelopeGap 13017 (61 / 100) 165 (17 / (100 * 13017)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13017

namespace BstLean.Part266.Row13017
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13017 165 ≤ (4308758021 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13017 165 ≤ (1437474493 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (345497517 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13017 165 ≤ (340499493 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 13017 165 ≤ (75705899 / 6250000000000000000)
  w2 : (tableEnvelope C).w2 13017 165 ≤ (221287983 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (4425719 / 1000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (4425719 / 1000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (679990637 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1049326243 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((45173 / 12500000) : ℝ) ≤ √(17 / (100 * 13017) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13017) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (210373929 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36877923939 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13017) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13017) ≤ (108643587 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13017) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13017 * (165 : ℝ) ^ 2 + 26 / (10 * 13017) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13017) : ℝ)) (tA 13017 * 165 ^ 2 + 26 / (10 * 13017)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((45173 / 12500000))) * ((4425719 / 1000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((45173 / 12500000)) ^ 3) * ((679990637 / 500000000000000000000000))) + ((1049326243 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((45173 / 12500000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13017) : ℝ)) d.D d.V d.P (√(tA 13017) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((45173 / 12500000)) ^ 2 * (((210373929 / 100000000000000)) * ((36877923939 / 1000000000000000000)))) + ((1049326243 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13017) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((45173 / 12500000)) * ((4425719 / 1000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13017) : ℝ)) (tA 13017 * 165 ^ 2 + 26 / (10 * 13017)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((4425719 / 1000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((45173 / 12500000)) ^ 2) * ((679990637 / 500000000000000000000000)) + ((1049326243 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13017) : ℝ)) (√(26 / (10 * 13017) : ℝ)) d.D d.V d.P (√(tA 13017) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((45173 / 12500000)) * (((210373929 / 100000000000000)) * ((36877923939 / 1000000000000000000))) + ((1049326243 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13017) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((4425719 / 1000000000000000000) : ℝ) + ((1049326243 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13017

namespace BstLean.Part266.Row13017
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13017 165 ∧
    0 ≤ (tableEnvelope C).f1 13017 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13017 165 ∧
    0 ≤ (tableEnvelope C).w1 13017 165 ∧ 0 ≤ (tableEnvelope C).w2 13017 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13017 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13017 165 ∧ 0 ≤ d.f1 13017 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13017 165 ∧ 0 ≤ d.w1 13017 165 ∧ 0 ≤ d.w2 13017 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13017 ≤ 2 * (228 / 100 : ℝ) / 13017 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13017 ≤ 2 * (370 / 100 : ℝ) / 13017 := by
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
    (completeRAData (tableEnvelope C) 13017 165).locationBound 13017 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13017 165).energyBound 13017 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13017 165) (d.f1 13017 165) d.f2 ≤
      32 * (((4308758021 / 1000000000000000000) : ℝ) + (1437474493 / 1000000000000000000) + (345497517 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13017 165) (d.w1 13017 165)
      (d.w2 13017 165) ≤
      32 * (((340499493 / 20000000000000000000) : ℝ) + (75705899 / 6250000000000000000) + (221287983 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13017 165) (d.f1 13017 165) d.f2 ≤
      ((4308758021 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4308758021 / 1000000000000000000)) * ((1437474493 / 1000000000000000000)) * (126 / 100) +
      2 * (((1437474493 / 1000000000000000000)) ^ 2 + 2 * ((4308758021 / 1000000000000000000)) * ((345497517 / 1000000000000000000))) +
      6 * ((1437474493 / 1000000000000000000)) * ((345497517 / 1000000000000000000)) * (126 / 100) + 8 * ((345497517 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13017 165) (d.f1 13017 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13017 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13017 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13017 165) (d.f1 13017 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13017 165) (d.w1 13017 165) (d.w2 13017 165)
  have hwexpr0 : 0 ≤ d.w0 13017 165 + d.w1 13017 165 * √(π / 2) +
      2 * d.w2 13017 165 + energyR16 13017 *
      radiusPolynomialRoot16 (d.w0 13017 165) (d.w1 13017 165) (d.w2 13017 165) := by
    positivity
  constructor
  · change (13017 : ℝ) ^ 8 * (mA 13017 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13017 165) (d.f1 13017 165) d.f2 + locationR16 13017 *
        radiusPolynomialRoot16 (d.f0 13017 165) (d.f1 13017 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13017 : ℝ) ^ 8 * (mA 13017 : ℝ) ^ 8 *
        ((((4308758021 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4308758021 / 1000000000000000000)) * ((1437474493 / 1000000000000000000)) * (126 / 100) +
          2 * (((1437474493 / 1000000000000000000)) ^ 2 + 2 * ((4308758021 / 1000000000000000000)) * ((345497517 / 1000000000000000000))) +
          6 * ((1437474493 / 1000000000000000000)) * ((345497517 / 1000000000000000000)) * (126 / 100) + 8 * ((345497517 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13017) *
          (32 * (((4308758021 / 1000000000000000000) : ℝ) + (1437474493 / 1000000000000000000) + (345497517 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13017 : ℝ) ^ 16 *
      (d.w0 13017 165 + d.w1 13017 165 * √(π / 2) + 2 * d.w2 13017 165 +
        energyR16 13017 * radiusPolynomialRoot16 (d.w0 13017 165) (d.w1 13017 165)
          (d.w2 13017 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13017 : ℝ) ^ 16 *
        (((340499493 / 20000000000000000000) : ℝ) + ((75705899 / 6250000000000000000)) * (126 / 100) + 2 * ((221287983 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13017) *
          (32 * (((340499493 / 20000000000000000000) : ℝ) + (75705899 / 6250000000000000000) + (221287983 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13017

/-! A coarse bound on the actual paper statistics constant at dimension 13018. -/
namespace BstLean.Part266.Row13018
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13016 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13016 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13016 128 ≤ (13270 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13270 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13018) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13018 : ℕ))
    (by norm_num : (13018 : ℕ) ≤ 16384)
  have ht : paperTail256 13018 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13018 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13018 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13018 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13018 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13018 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13016 128 * √(2 / (13018 : ℝ)) *
      (√(13018 : ℝ) + paperT0 13018 + paperTail256 13018) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13018 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13018 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13018 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13016 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13016 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13018 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13018

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13018
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13018 (61 / 100) 165 (17 / (100 * 13018)) (26 / (10 * 13018)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13018 (61 / 100) 165 (17 / (100 * 13018)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (55308739 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1359563429 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (131084431 / 31250000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13018 / 13018 * (61 / 100)) ^ 4 * inverseRadius8 (13018 - 1) /
            envelopeGap 13018 (61 / 100) 165 (17 / (100 * 13018)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13018

namespace BstLean.Part266.Row13018
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13018 165 ≤ (430793123 / 100000000000000000)
  f1 : (tableEnvelope C).f1 13018 165 ≤ (1437198593 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (172715593 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13018 165 ≤ (1702105271 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13018 165 ≤ (242203063 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 13018 165 ≤ (55309247 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (55308739 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (55308739 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1359563429 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (131084431 / 31250000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3613701 / 1000000000) : ℝ) ≤ √(17 / (100 * 13018) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13018) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (26293711 / 12500000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18436129129 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13018) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13018) ≤ (108635241 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13018) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13018 * (165 : ℝ) ^ 2 + 26 / (10 * 13018) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13018) : ℝ)) (tA 13018 * 165 ^ 2 + 26 / (10 * 13018)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3613701 / 1000000000))) * ((55308739 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3613701 / 1000000000)) ^ 3) * ((1359563429 / 1000000000000000000000000))) + ((131084431 / 31250000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3613701 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13018) : ℝ)) d.D d.V d.P (√(tA 13018) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3613701 / 1000000000)) ^ 2 * (((26293711 / 12500000000000)) * ((18436129129 / 500000000000000000)))) + ((131084431 / 31250000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13018) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3613701 / 1000000000)) * ((55308739 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13018) : ℝ)) (tA 13018 * 165 ^ 2 + 26 / (10 * 13018)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((55308739 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3613701 / 1000000000)) ^ 2) * ((1359563429 / 1000000000000000000000000)) + ((131084431 / 31250000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13018) : ℝ)) (√(26 / (10 * 13018) : ℝ)) d.D d.V d.P (√(tA 13018) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3613701 / 1000000000)) * (((26293711 / 12500000000000)) * ((18436129129 / 500000000000000000))) + ((131084431 / 31250000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13018) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((55308739 / 12500000000000000000) : ℝ) + ((131084431 / 31250000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13018

namespace BstLean.Part266.Row13018
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13018 165 ∧
    0 ≤ (tableEnvelope C).f1 13018 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13018 165 ∧
    0 ≤ (tableEnvelope C).w1 13018 165 ∧ 0 ≤ (tableEnvelope C).w2 13018 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13018 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13018 165 ∧ 0 ≤ d.f1 13018 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13018 165 ∧ 0 ≤ d.w1 13018 165 ∧ 0 ≤ d.w2 13018 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13018 ≤ 2 * (228 / 100 : ℝ) / 13018 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13018 ≤ 2 * (370 / 100 : ℝ) / 13018 := by
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
    (completeRAData (tableEnvelope C) 13018 165).locationBound 13018 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13018 165).energyBound 13018 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13018 165) (d.f1 13018 165) d.f2 ≤
      32 * (((430793123 / 100000000000000000) : ℝ) + (1437198593 / 1000000000000000000) + (172715593 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13018 165) (d.w1 13018 165)
      (d.w2 13018 165) ≤
      32 * (((1702105271 / 100000000000000000000) : ℝ) + (242203063 / 20000000000000000000) + (55309247 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13018 165) (d.f1 13018 165) d.f2 ≤
      ((430793123 / 100000000000000000) : ℝ) ^ 2 + 2 * ((430793123 / 100000000000000000)) * ((1437198593 / 1000000000000000000)) * (126 / 100) +
      2 * (((1437198593 / 1000000000000000000)) ^ 2 + 2 * ((430793123 / 100000000000000000)) * ((172715593 / 500000000000000000))) +
      6 * ((1437198593 / 1000000000000000000)) * ((172715593 / 500000000000000000)) * (126 / 100) + 8 * ((172715593 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13018 165) (d.f1 13018 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13018 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13018 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13018 165) (d.f1 13018 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13018 165) (d.w1 13018 165) (d.w2 13018 165)
  have hwexpr0 : 0 ≤ d.w0 13018 165 + d.w1 13018 165 * √(π / 2) +
      2 * d.w2 13018 165 + energyR16 13018 *
      radiusPolynomialRoot16 (d.w0 13018 165) (d.w1 13018 165) (d.w2 13018 165) := by
    positivity
  constructor
  · change (13018 : ℝ) ^ 8 * (mA 13018 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13018 165) (d.f1 13018 165) d.f2 + locationR16 13018 *
        radiusPolynomialRoot16 (d.f0 13018 165) (d.f1 13018 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13018 : ℝ) ^ 8 * (mA 13018 : ℝ) ^ 8 *
        ((((430793123 / 100000000000000000) : ℝ) ^ 2 + 2 * ((430793123 / 100000000000000000)) * ((1437198593 / 1000000000000000000)) * (126 / 100) +
          2 * (((1437198593 / 1000000000000000000)) ^ 2 + 2 * ((430793123 / 100000000000000000)) * ((172715593 / 500000000000000000))) +
          6 * ((1437198593 / 1000000000000000000)) * ((172715593 / 500000000000000000)) * (126 / 100) + 8 * ((172715593 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13018) *
          (32 * (((430793123 / 100000000000000000) : ℝ) + (1437198593 / 1000000000000000000) + (172715593 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13018 : ℝ) ^ 16 *
      (d.w0 13018 165 + d.w1 13018 165 * √(π / 2) + 2 * d.w2 13018 165 +
        energyR16 13018 * radiusPolynomialRoot16 (d.w0 13018 165) (d.w1 13018 165)
          (d.w2 13018 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13018 : ℝ) ^ 16 *
        (((1702105271 / 100000000000000000000) : ℝ) + ((242203063 / 20000000000000000000)) * (126 / 100) + 2 * ((55309247 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13018) *
          (32 * (((1702105271 / 100000000000000000000) : ℝ) + (242203063 / 20000000000000000000) + (55309247 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13018

/-! A coarse bound on the actual paper statistics constant at dimension 13019. -/
namespace BstLean.Part266.Row13019
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13017 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13017 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13017 128 ≤ (13271 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13271 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13019) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13019 : ℕ))
    (by norm_num : (13019 : ℕ) ≤ 16384)
  have ht : paperTail256 13019 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13019 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13019 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13019 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13019 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13019 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13017 128 * √(2 / (13019 : ℝ)) *
      (√(13019 : ℝ) + paperT0 13019 + paperTail256 13019) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13019 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13019 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13019 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13017 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13017 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13019 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13019

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13019
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13019 (61 / 100) 165 (17 / (100 * 13019)) (26 / (10 * 13019)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13019 (61 / 100) 165 (17 / (100 * 13019)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (88473591 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (84946609 / 62500000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (419210043 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13019 / 13019 * (61 / 100)) ^ 4 * inverseRadius8 (13019 - 1) /
            envelopeGap 13019 (61 / 100) 165 (17 / (100 * 13019)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13019

namespace BstLean.Part266.Row13019
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13019 165 ≤ (2153550637 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13019 165 ≤ (718460991 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (172682389 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13019 165 ≤ (170171251 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 13019 165 ≤ (1210735999 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13019 165 ≤ (27648251 / 6250000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (88473591 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (88473591 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (84946609 / 62500000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (419210043 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3613563 / 1000000000) : ℝ) ≤ √(17 / (100 * 13019) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13019) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1051627257 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9216648469 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13019) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13019) ≤ (108626897 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13019) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13019 * (165 : ℝ) ^ 2 + 26 / (10 * 13019) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13019) : ℝ)) (tA 13019 * 165 ^ 2 + 26 / (10 * 13019)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3613563 / 1000000000))) * ((88473591 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3613563 / 1000000000)) ^ 3) * ((84946609 / 62500000000000000000000))) + ((419210043 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3613563 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13019) : ℝ)) d.D d.V d.P (√(tA 13019) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3613563 / 1000000000)) ^ 2 * (((1051627257 / 500000000000000)) * ((9216648469 / 250000000000000000)))) + ((419210043 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13019) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3613563 / 1000000000)) * ((88473591 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13019) : ℝ)) (tA 13019 * 165 ^ 2 + 26 / (10 * 13019)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((88473591 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3613563 / 1000000000)) ^ 2) * ((84946609 / 62500000000000000000000)) + ((419210043 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13019) : ℝ)) (√(26 / (10 * 13019) : ℝ)) d.D d.V d.P (√(tA 13019) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3613563 / 1000000000)) * (((1051627257 / 500000000000000)) * ((9216648469 / 250000000000000000))) + ((419210043 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13019) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((88473591 / 20000000000000000000) : ℝ) + ((419210043 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13019

namespace BstLean.Part266.Row13019
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13019 165 ∧
    0 ≤ (tableEnvelope C).f1 13019 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13019 165 ∧
    0 ≤ (tableEnvelope C).w1 13019 165 ∧ 0 ≤ (tableEnvelope C).w2 13019 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13019 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13019 165 ∧ 0 ≤ d.f1 13019 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13019 165 ∧ 0 ≤ d.w1 13019 165 ∧ 0 ≤ d.w2 13019 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13019 ≤ 2 * (228 / 100 : ℝ) / 13019 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13019 ≤ 2 * (370 / 100 : ℝ) / 13019 := by
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
    (completeRAData (tableEnvelope C) 13019 165).locationBound 13019 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13019 165).energyBound 13019 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13019 165) (d.f1 13019 165) d.f2 ≤
      32 * (((2153550637 / 500000000000000000) : ℝ) + (718460991 / 500000000000000000) + (172682389 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13019 165) (d.w1 13019 165)
      (d.w2 13019 165) ≤
      32 * (((170171251 / 10000000000000000000) : ℝ) + (1210735999 / 100000000000000000000) + (27648251 / 6250000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13019 165) (d.f1 13019 165) d.f2 ≤
      ((2153550637 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2153550637 / 500000000000000000)) * ((718460991 / 500000000000000000)) * (126 / 100) +
      2 * (((718460991 / 500000000000000000)) ^ 2 + 2 * ((2153550637 / 500000000000000000)) * ((172682389 / 500000000000000000))) +
      6 * ((718460991 / 500000000000000000)) * ((172682389 / 500000000000000000)) * (126 / 100) + 8 * ((172682389 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13019 165) (d.f1 13019 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13019 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13019 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13019 165) (d.f1 13019 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13019 165) (d.w1 13019 165) (d.w2 13019 165)
  have hwexpr0 : 0 ≤ d.w0 13019 165 + d.w1 13019 165 * √(π / 2) +
      2 * d.w2 13019 165 + energyR16 13019 *
      radiusPolynomialRoot16 (d.w0 13019 165) (d.w1 13019 165) (d.w2 13019 165) := by
    positivity
  constructor
  · change (13019 : ℝ) ^ 8 * (mA 13019 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13019 165) (d.f1 13019 165) d.f2 + locationR16 13019 *
        radiusPolynomialRoot16 (d.f0 13019 165) (d.f1 13019 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13019 : ℝ) ^ 8 * (mA 13019 : ℝ) ^ 8 *
        ((((2153550637 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2153550637 / 500000000000000000)) * ((718460991 / 500000000000000000)) * (126 / 100) +
          2 * (((718460991 / 500000000000000000)) ^ 2 + 2 * ((2153550637 / 500000000000000000)) * ((172682389 / 500000000000000000))) +
          6 * ((718460991 / 500000000000000000)) * ((172682389 / 500000000000000000)) * (126 / 100) + 8 * ((172682389 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13019) *
          (32 * (((2153550637 / 500000000000000000) : ℝ) + (718460991 / 500000000000000000) + (172682389 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13019 : ℝ) ^ 16 *
      (d.w0 13019 165 + d.w1 13019 165 * √(π / 2) + 2 * d.w2 13019 165 +
        energyR16 13019 * radiusPolynomialRoot16 (d.w0 13019 165) (d.w1 13019 165)
          (d.w2 13019 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13019 : ℝ) ^ 16 *
        (((170171251 / 10000000000000000000) : ℝ) + ((1210735999 / 100000000000000000000)) * (126 / 100) + 2 * ((27648251 / 6250000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13019) *
          (32 * (((170171251 / 10000000000000000000) : ℝ) + (1210735999 / 100000000000000000000) + (27648251 / 6250000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13019

/-! A coarse bound on the actual paper statistics constant at dimension 13020. -/
namespace BstLean.Part266.Row13020
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13018 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13018 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13018 128 ≤ (13272 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13272 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13020) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13020 : ℕ))
    (by norm_num : (13020 : ℕ) ≤ 16384)
  have ht : paperTail256 13020 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13020 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13020 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13020 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13020 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13020 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13018 128 * √(2 / (13020 : ℝ)) *
      (√(13020 : ℝ) + paperT0 13020 + paperTail256 13020) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13020 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13020 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13020 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13018 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13018 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13020 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13020

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13020
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13020 (61 / 100) 165 (17 / (100 * 13020)) (26 / (10 * 13020)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13020 (61 / 100) 165 (17 / (100 * 13020)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (44226603 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (67936411 / 50000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1047375221 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13020 / 13020 * (61 / 100)) ^ 4 * inverseRadius8 (13020 - 1) /
            envelopeGap 13020 (61 / 100) 165 (17 / (100 * 13020)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13020

namespace BstLean.Part266.Row13020
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13020 165 ≤ (2153137519 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13020 165 ≤ (89790391 / 62500000000000000)
  f2 : (tableEnvelope C).f2 ≤ (172649243 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13020 165 ≤ (1701320579 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13020 165 ≤ (151307139 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 13020 165 ≤ (442270089 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (44226603 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (44226603 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (67936411 / 50000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1047375221 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((225839 / 62500000) : ℝ) ≤ √(17 / (100 * 13020) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13020) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2103012197 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4607616351 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13020) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13020) ≤ (54309277 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13020) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13020 * (165 : ℝ) ^ 2 + 26 / (10 * 13020) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13020) : ℝ)) (tA 13020 * 165 ^ 2 + 26 / (10 * 13020)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((225839 / 62500000))) * ((44226603 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((225839 / 62500000)) ^ 3) * ((67936411 / 50000000000000000000000))) + ((1047375221 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((225839 / 62500000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13020) : ℝ)) d.D d.V d.P (√(tA 13020) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((225839 / 62500000)) ^ 2 * (((2103012197 / 1000000000000000)) * ((4607616351 / 125000000000000000)))) + ((1047375221 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13020) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((225839 / 62500000)) * ((44226603 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13020) : ℝ)) (tA 13020 * 165 ^ 2 + 26 / (10 * 13020)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((44226603 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((225839 / 62500000)) ^ 2) * ((67936411 / 50000000000000000000000)) + ((1047375221 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13020) : ℝ)) (√(26 / (10 * 13020) : ℝ)) d.D d.V d.P (√(tA 13020) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((225839 / 62500000)) * (((2103012197 / 1000000000000000)) * ((4607616351 / 125000000000000000))) + ((1047375221 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13020) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((44226603 / 10000000000000000000) : ℝ) + ((1047375221 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13020

namespace BstLean.Part266.Row13020
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13020 165 ∧
    0 ≤ (tableEnvelope C).f1 13020 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13020 165 ∧
    0 ≤ (tableEnvelope C).w1 13020 165 ∧ 0 ≤ (tableEnvelope C).w2 13020 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13020 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13020 165 ∧ 0 ≤ d.f1 13020 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13020 165 ∧ 0 ≤ d.w1 13020 165 ∧ 0 ≤ d.w2 13020 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13020 ≤ 2 * (228 / 100 : ℝ) / 13020 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13020 ≤ 2 * (370 / 100 : ℝ) / 13020 := by
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
    (completeRAData (tableEnvelope C) 13020 165).locationBound 13020 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13020 165).energyBound 13020 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13020 165) (d.f1 13020 165) d.f2 ≤
      32 * (((2153137519 / 500000000000000000) : ℝ) + (89790391 / 62500000000000000) + (172649243 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13020 165) (d.w1 13020 165)
      (d.w2 13020 165) ≤
      32 * (((1701320579 / 100000000000000000000) : ℝ) + (151307139 / 12500000000000000000) + (442270089 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13020 165) (d.f1 13020 165) d.f2 ≤
      ((2153137519 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2153137519 / 500000000000000000)) * ((89790391 / 62500000000000000)) * (126 / 100) +
      2 * (((89790391 / 62500000000000000)) ^ 2 + 2 * ((2153137519 / 500000000000000000)) * ((172649243 / 500000000000000000))) +
      6 * ((89790391 / 62500000000000000)) * ((172649243 / 500000000000000000)) * (126 / 100) + 8 * ((172649243 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13020 165) (d.f1 13020 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13020 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13020 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13020 165) (d.f1 13020 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13020 165) (d.w1 13020 165) (d.w2 13020 165)
  have hwexpr0 : 0 ≤ d.w0 13020 165 + d.w1 13020 165 * √(π / 2) +
      2 * d.w2 13020 165 + energyR16 13020 *
      radiusPolynomialRoot16 (d.w0 13020 165) (d.w1 13020 165) (d.w2 13020 165) := by
    positivity
  constructor
  · change (13020 : ℝ) ^ 8 * (mA 13020 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13020 165) (d.f1 13020 165) d.f2 + locationR16 13020 *
        radiusPolynomialRoot16 (d.f0 13020 165) (d.f1 13020 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13020 : ℝ) ^ 8 * (mA 13020 : ℝ) ^ 8 *
        ((((2153137519 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2153137519 / 500000000000000000)) * ((89790391 / 62500000000000000)) * (126 / 100) +
          2 * (((89790391 / 62500000000000000)) ^ 2 + 2 * ((2153137519 / 500000000000000000)) * ((172649243 / 500000000000000000))) +
          6 * ((89790391 / 62500000000000000)) * ((172649243 / 500000000000000000)) * (126 / 100) + 8 * ((172649243 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13020) *
          (32 * (((2153137519 / 500000000000000000) : ℝ) + (89790391 / 62500000000000000) + (172649243 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13020 : ℝ) ^ 16 *
      (d.w0 13020 165 + d.w1 13020 165 * √(π / 2) + 2 * d.w2 13020 165 +
        energyR16 13020 * radiusPolynomialRoot16 (d.w0 13020 165) (d.w1 13020 165)
          (d.w2 13020 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13020 : ℝ) ^ 16 *
        (((1701320579 / 100000000000000000000) : ℝ) + ((151307139 / 12500000000000000000)) * (126 / 100) + 2 * ((442270089 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13020) *
          (32 * (((1701320579 / 100000000000000000000) : ℝ) + (151307139 / 12500000000000000000) + (442270089 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13020

/-! A coarse bound on the actual paper statistics constant at dimension 13021. -/
namespace BstLean.Part266.Row13021
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13019 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13019 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13019 128 ≤ (13273 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13273 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13021) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13021 : ℕ))
    (by norm_num : (13021 : ℕ) ≤ 16384)
  have ht : paperTail256 13021 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13021 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13021 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13021 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13021 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13021 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13019 128 * √(2 / (13021 : ℝ)) *
      (√(13021 : ℝ) + paperT0 13021 + paperTail256 13021) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13021 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13021 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13021 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13019 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13019 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13021 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13021

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13021
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13021 (61 / 100) 165 (17 / (100 * 13021)) (26 / (10 * 13021)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13021 (61 / 100) 165 (17 / (100 * 13021)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (88432827 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (169788857 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4186903153 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13021 / 13021 * (61 / 100)) ^ 4 * inverseRadius8 (13021 - 1) /
            envelopeGap 13021 (61 / 100) 165 (17 / (100 * 13021)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13021

namespace BstLean.Part266.Row13021
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13021 165 ≤ (2152724539 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13021 165 ≤ (287274123 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (86308053 / 250000000000000000)
  w0 : (tableEnvelope C).w0 13021 165 ≤ (1700928779 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13021 165 ≤ (605089157 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13021 165 ≤ (442168191 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (88432827 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (88432827 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (169788857 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4186903153 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((722657 / 200000000) : ℝ) ≤ √(17 / (100 * 13021) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13021) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (525692481 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (460690863 / 12500000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13021) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13021) ≤ (27152553 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13021) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13021 * (165 : ℝ) ^ 2 + 26 / (10 * 13021) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13021) : ℝ)) (tA 13021 * 165 ^ 2 + 26 / (10 * 13021)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((722657 / 200000000))) * ((88432827 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((722657 / 200000000)) ^ 3) * ((169788857 / 125000000000000000000000))) + ((4186903153 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((722657 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13021) : ℝ)) d.D d.V d.P (√(tA 13021) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((722657 / 200000000)) ^ 2 * (((525692481 / 250000000000000)) * ((460690863 / 12500000000000000)))) + ((4186903153 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13021) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((722657 / 200000000)) * ((88432827 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13021) : ℝ)) (tA 13021 * 165 ^ 2 + 26 / (10 * 13021)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((88432827 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((722657 / 200000000)) ^ 2) * ((169788857 / 125000000000000000000000)) + ((4186903153 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13021) : ℝ)) (√(26 / (10 * 13021) : ℝ)) d.D d.V d.P (√(tA 13021) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((722657 / 200000000)) * (((525692481 / 250000000000000)) * ((460690863 / 12500000000000000))) + ((4186903153 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13021) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((88432827 / 20000000000000000000) : ℝ) + ((4186903153 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13021

namespace BstLean.Part266.Row13021
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13021 165 ∧
    0 ≤ (tableEnvelope C).f1 13021 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13021 165 ∧
    0 ≤ (tableEnvelope C).w1 13021 165 ∧ 0 ≤ (tableEnvelope C).w2 13021 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13021 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13021 165 ∧ 0 ≤ d.f1 13021 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13021 165 ∧ 0 ≤ d.w1 13021 165 ∧ 0 ≤ d.w2 13021 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13021 ≤ 2 * (228 / 100 : ℝ) / 13021 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13021 ≤ 2 * (370 / 100 : ℝ) / 13021 := by
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
    (completeRAData (tableEnvelope C) 13021 165).locationBound 13021 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13021 165).energyBound 13021 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13021 165) (d.f1 13021 165) d.f2 ≤
      32 * (((2152724539 / 500000000000000000) : ℝ) + (287274123 / 200000000000000000) + (86308053 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13021 165) (d.w1 13021 165)
      (d.w2 13021 165) ≤
      32 * (((1700928779 / 100000000000000000000) : ℝ) + (605089157 / 50000000000000000000) + (442168191 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13021 165) (d.f1 13021 165) d.f2 ≤
      ((2152724539 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2152724539 / 500000000000000000)) * ((287274123 / 200000000000000000)) * (126 / 100) +
      2 * (((287274123 / 200000000000000000)) ^ 2 + 2 * ((2152724539 / 500000000000000000)) * ((86308053 / 250000000000000000))) +
      6 * ((287274123 / 200000000000000000)) * ((86308053 / 250000000000000000)) * (126 / 100) + 8 * ((86308053 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13021 165) (d.f1 13021 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13021 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13021 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13021 165) (d.f1 13021 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13021 165) (d.w1 13021 165) (d.w2 13021 165)
  have hwexpr0 : 0 ≤ d.w0 13021 165 + d.w1 13021 165 * √(π / 2) +
      2 * d.w2 13021 165 + energyR16 13021 *
      radiusPolynomialRoot16 (d.w0 13021 165) (d.w1 13021 165) (d.w2 13021 165) := by
    positivity
  constructor
  · change (13021 : ℝ) ^ 8 * (mA 13021 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13021 165) (d.f1 13021 165) d.f2 + locationR16 13021 *
        radiusPolynomialRoot16 (d.f0 13021 165) (d.f1 13021 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13021 : ℝ) ^ 8 * (mA 13021 : ℝ) ^ 8 *
        ((((2152724539 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2152724539 / 500000000000000000)) * ((287274123 / 200000000000000000)) * (126 / 100) +
          2 * (((287274123 / 200000000000000000)) ^ 2 + 2 * ((2152724539 / 500000000000000000)) * ((86308053 / 250000000000000000))) +
          6 * ((287274123 / 200000000000000000)) * ((86308053 / 250000000000000000)) * (126 / 100) + 8 * ((86308053 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13021) *
          (32 * (((2152724539 / 500000000000000000) : ℝ) + (287274123 / 200000000000000000) + (86308053 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13021 : ℝ) ^ 16 *
      (d.w0 13021 165 + d.w1 13021 165 * √(π / 2) + 2 * d.w2 13021 165 +
        energyR16 13021 * radiusPolynomialRoot16 (d.w0 13021 165) (d.w1 13021 165)
          (d.w2 13021 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13021 : ℝ) ^ 16 *
        (((1700928779 / 100000000000000000000) : ℝ) + ((605089157 / 50000000000000000000)) * (126 / 100) + 2 * ((442168191 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13021) *
          (32 * (((1700928779 / 100000000000000000000) : ℝ) + (605089157 / 50000000000000000000) + (442168191 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13021

/-! A coarse bound on the actual paper statistics constant at dimension 13022. -/
namespace BstLean.Part266.Row13022
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13020 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13020 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13020 128 ≤ (13274 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13274 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13022) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13022 : ℕ))
    (by norm_num : (13022 : ℕ) ≤ 16384)
  have ht : paperTail256 13022 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13022 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13022 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13022 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13022 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13022 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13020 128 * √(2 / (13022 : ℝ)) *
      (√(13022 : ℝ) + paperT0 13022 + paperTail256 13022) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13022 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13022 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13022 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13020 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13020 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13022 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13022

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13022
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13022 (61 / 100) 165 (17 / (100 * 13022)) (26 / (10 * 13022)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13022 (61 / 100) 165 (17 / (100 * 13022)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (6907223 / 1562500000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (339473413 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1046076809 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13022 / 13022 * (61 / 100)) ^ 4 * inverseRadius8 (13022 - 1) /
            envelopeGap 13022 (61 / 100) 165 (17 / (100 * 13022)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13022

namespace BstLean.Part266.Row13022
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13022 165 ≤ (2152311697 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13022 165 ≤ (1436095061 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (172582979 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13022 165 ≤ (170053711 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 13022 165 ≤ (1209899607 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13022 165 ≤ (221033163 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (6907223 / 1562500000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (6907223 / 1562500000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (339473413 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1046076809 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1806573 / 500000000) : ℝ) ≤ √(17 / (100 * 13022) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13022) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1051263849 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18424804287 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13022) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13022) ≤ (108601871 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13022) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13022 * (165 : ℝ) ^ 2 + 26 / (10 * 13022) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13022) : ℝ)) (tA 13022 * 165 ^ 2 + 26 / (10 * 13022)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1806573 / 500000000))) * ((6907223 / 1562500000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1806573 / 500000000)) ^ 3) * ((339473413 / 250000000000000000000000))) + ((1046076809 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1806573 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13022) : ℝ)) d.D d.V d.P (√(tA 13022) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1806573 / 500000000)) ^ 2 * (((1051263849 / 500000000000000)) * ((18424804287 / 500000000000000000)))) + ((1046076809 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13022) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1806573 / 500000000)) * ((6907223 / 1562500000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13022) : ℝ)) (tA 13022 * 165 ^ 2 + 26 / (10 * 13022)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((6907223 / 1562500000000000000) : ℝ) + (24198 / 100000) / (2 * ((1806573 / 500000000)) ^ 2) * ((339473413 / 250000000000000000000000)) + ((1046076809 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13022) : ℝ)) (√(26 / (10 * 13022) : ℝ)) d.D d.V d.P (√(tA 13022) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1806573 / 500000000)) * (((1051263849 / 500000000000000)) * ((18424804287 / 500000000000000000))) + ((1046076809 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13022) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((6907223 / 1562500000000000000) : ℝ) + ((1046076809 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13022

namespace BstLean.Part266.Row13022
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13022 165 ∧
    0 ≤ (tableEnvelope C).f1 13022 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13022 165 ∧
    0 ≤ (tableEnvelope C).w1 13022 165 ∧ 0 ≤ (tableEnvelope C).w2 13022 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13022 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13022 165 ∧ 0 ≤ d.f1 13022 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13022 165 ∧ 0 ≤ d.w1 13022 165 ∧ 0 ≤ d.w2 13022 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13022 ≤ 2 * (228 / 100 : ℝ) / 13022 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13022 ≤ 2 * (370 / 100 : ℝ) / 13022 := by
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
    (completeRAData (tableEnvelope C) 13022 165).locationBound 13022 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13022 165).energyBound 13022 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13022 165) (d.f1 13022 165) d.f2 ≤
      32 * (((2152311697 / 500000000000000000) : ℝ) + (1436095061 / 1000000000000000000) + (172582979 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13022 165) (d.w1 13022 165)
      (d.w2 13022 165) ≤
      32 * (((170053711 / 10000000000000000000) : ℝ) + (1209899607 / 100000000000000000000) + (221033163 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13022 165) (d.f1 13022 165) d.f2 ≤
      ((2152311697 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2152311697 / 500000000000000000)) * ((1436095061 / 1000000000000000000)) * (126 / 100) +
      2 * (((1436095061 / 1000000000000000000)) ^ 2 + 2 * ((2152311697 / 500000000000000000)) * ((172582979 / 500000000000000000))) +
      6 * ((1436095061 / 1000000000000000000)) * ((172582979 / 500000000000000000)) * (126 / 100) + 8 * ((172582979 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13022 165) (d.f1 13022 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13022 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13022 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13022 165) (d.f1 13022 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13022 165) (d.w1 13022 165) (d.w2 13022 165)
  have hwexpr0 : 0 ≤ d.w0 13022 165 + d.w1 13022 165 * √(π / 2) +
      2 * d.w2 13022 165 + energyR16 13022 *
      radiusPolynomialRoot16 (d.w0 13022 165) (d.w1 13022 165) (d.w2 13022 165) := by
    positivity
  constructor
  · change (13022 : ℝ) ^ 8 * (mA 13022 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13022 165) (d.f1 13022 165) d.f2 + locationR16 13022 *
        radiusPolynomialRoot16 (d.f0 13022 165) (d.f1 13022 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13022 : ℝ) ^ 8 * (mA 13022 : ℝ) ^ 8 *
        ((((2152311697 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2152311697 / 500000000000000000)) * ((1436095061 / 1000000000000000000)) * (126 / 100) +
          2 * (((1436095061 / 1000000000000000000)) ^ 2 + 2 * ((2152311697 / 500000000000000000)) * ((172582979 / 500000000000000000))) +
          6 * ((1436095061 / 1000000000000000000)) * ((172582979 / 500000000000000000)) * (126 / 100) + 8 * ((172582979 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13022) *
          (32 * (((2152311697 / 500000000000000000) : ℝ) + (1436095061 / 1000000000000000000) + (172582979 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13022 : ℝ) ^ 16 *
      (d.w0 13022 165 + d.w1 13022 165 * √(π / 2) + 2 * d.w2 13022 165 +
        energyR16 13022 * radiusPolynomialRoot16 (d.w0 13022 165) (d.w1 13022 165)
          (d.w2 13022 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13022 : ℝ) ^ 16 *
        (((170053711 / 10000000000000000000) : ℝ) + ((1209899607 / 100000000000000000000)) * (126 / 100) + 2 * ((221033163 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13022) *
          (32 * (((170053711 / 10000000000000000000) : ℝ) + (1209899607 / 100000000000000000000) + (221033163 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13022

/-! A coarse bound on the actual paper statistics constant at dimension 13023. -/
namespace BstLean.Part266.Row13023
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13021 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13021 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13021 128 ≤ (13275 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13275 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13023) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13023 : ℕ))
    (by norm_num : (13023 : ℕ) ≤ 16384)
  have ht : paperTail256 13023 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13023 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13023 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13023 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13023 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13023 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13021 128 * √(2 / (13023 : ℝ)) *
      (√(13023 : ℝ) + paperT0 13023 + paperTail256 13023) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13023 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13023 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13023 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13021 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13021 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13023 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13023

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13023
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13023 (61 / 100) 165 (17 / (100 * 13023)) (26 / (10 * 13023)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13023 (61 / 100) 165 (17 / (100 * 13023)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (441960441 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1357476609 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1045428283 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13023 / 13023 * (61 / 100)) ^ 4 * inverseRadius8 (13023 - 1) /
            envelopeGap 13023 (61 / 100) 165 (17 / (100 * 13023)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13023

namespace BstLean.Part266.Row13023
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13023 165 ≤ (537974319 / 125000000000000000)
  f1 : (tableEnvelope C).f1 13023 165 ≤ (1435818801 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (86274907 / 250000000000000000)
  w0 : (tableEnvelope C).w0 13023 165 ≤ (1700144877 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13023 165 ≤ (604810329 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13023 165 ≤ (110491123 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (441960441 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (441960441 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1357476609 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1045428283 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((225813 / 62500000) : ℝ) ≤ √(17 / (100 * 13023) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13023) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2102285521 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18421974711 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13023) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13023) ≤ (27148383 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13023) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13023 * (165 : ℝ) ^ 2 + 26 / (10 * 13023) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13023) : ℝ)) (tA 13023 * 165 ^ 2 + 26 / (10 * 13023)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((225813 / 62500000))) * ((441960441 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((225813 / 62500000)) ^ 3) * ((1357476609 / 1000000000000000000000000))) + ((1045428283 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((225813 / 62500000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13023) : ℝ)) d.D d.V d.P (√(tA 13023) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((225813 / 62500000)) ^ 2 * (((2102285521 / 1000000000000000)) * ((18421974711 / 500000000000000000)))) + ((1045428283 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13023) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((225813 / 62500000)) * ((441960441 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13023) : ℝ)) (tA 13023 * 165 ^ 2 + 26 / (10 * 13023)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((441960441 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((225813 / 62500000)) ^ 2) * ((1357476609 / 1000000000000000000000000)) + ((1045428283 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13023) : ℝ)) (√(26 / (10 * 13023) : ℝ)) d.D d.V d.P (√(tA 13023) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((225813 / 62500000)) * (((2102285521 / 1000000000000000)) * ((18421974711 / 500000000000000000))) + ((1045428283 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13023) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((441960441 / 100000000000000000000) : ℝ) + ((1045428283 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13023

namespace BstLean.Part266.Row13023
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13023 165 ∧
    0 ≤ (tableEnvelope C).f1 13023 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13023 165 ∧
    0 ≤ (tableEnvelope C).w1 13023 165 ∧ 0 ≤ (tableEnvelope C).w2 13023 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13023 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13023 165 ∧ 0 ≤ d.f1 13023 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13023 165 ∧ 0 ≤ d.w1 13023 165 ∧ 0 ≤ d.w2 13023 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13023 ≤ 2 * (228 / 100 : ℝ) / 13023 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13023 ≤ 2 * (370 / 100 : ℝ) / 13023 := by
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
    (completeRAData (tableEnvelope C) 13023 165).locationBound 13023 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13023 165).energyBound 13023 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13023 165) (d.f1 13023 165) d.f2 ≤
      32 * (((537974319 / 125000000000000000) : ℝ) + (1435818801 / 1000000000000000000) + (86274907 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13023 165) (d.w1 13023 165)
      (d.w2 13023 165) ≤
      32 * (((1700144877 / 100000000000000000000) : ℝ) + (604810329 / 50000000000000000000) + (110491123 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13023 165) (d.f1 13023 165) d.f2 ≤
      ((537974319 / 125000000000000000) : ℝ) ^ 2 + 2 * ((537974319 / 125000000000000000)) * ((1435818801 / 1000000000000000000)) * (126 / 100) +
      2 * (((1435818801 / 1000000000000000000)) ^ 2 + 2 * ((537974319 / 125000000000000000)) * ((86274907 / 250000000000000000))) +
      6 * ((1435818801 / 1000000000000000000)) * ((86274907 / 250000000000000000)) * (126 / 100) + 8 * ((86274907 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13023 165) (d.f1 13023 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13023 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13023 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13023 165) (d.f1 13023 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13023 165) (d.w1 13023 165) (d.w2 13023 165)
  have hwexpr0 : 0 ≤ d.w0 13023 165 + d.w1 13023 165 * √(π / 2) +
      2 * d.w2 13023 165 + energyR16 13023 *
      radiusPolynomialRoot16 (d.w0 13023 165) (d.w1 13023 165) (d.w2 13023 165) := by
    positivity
  constructor
  · change (13023 : ℝ) ^ 8 * (mA 13023 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13023 165) (d.f1 13023 165) d.f2 + locationR16 13023 *
        radiusPolynomialRoot16 (d.f0 13023 165) (d.f1 13023 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13023 : ℝ) ^ 8 * (mA 13023 : ℝ) ^ 8 *
        ((((537974319 / 125000000000000000) : ℝ) ^ 2 + 2 * ((537974319 / 125000000000000000)) * ((1435818801 / 1000000000000000000)) * (126 / 100) +
          2 * (((1435818801 / 1000000000000000000)) ^ 2 + 2 * ((537974319 / 125000000000000000)) * ((86274907 / 250000000000000000))) +
          6 * ((1435818801 / 1000000000000000000)) * ((86274907 / 250000000000000000)) * (126 / 100) + 8 * ((86274907 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13023) *
          (32 * (((537974319 / 125000000000000000) : ℝ) + (1435818801 / 1000000000000000000) + (86274907 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13023 : ℝ) ^ 16 *
      (d.w0 13023 165 + d.w1 13023 165 * √(π / 2) + 2 * d.w2 13023 165 +
        energyR16 13023 * radiusPolynomialRoot16 (d.w0 13023 165) (d.w1 13023 165)
          (d.w2 13023 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13023 : ℝ) ^ 16 *
        (((1700144877 / 100000000000000000000) : ℝ) + ((604810329 / 50000000000000000000)) * (126 / 100) + 2 * ((110491123 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13023) *
          (32 * (((1700144877 / 100000000000000000000) : ℝ) + (604810329 / 50000000000000000000) + (110491123 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13023

/-! A coarse bound on the actual paper statistics constant at dimension 13024. -/
namespace BstLean.Part266.Row13024
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13022 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13022 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13022 128 ≤ (13276 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13276 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13024) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13024 : ℕ))
    (by norm_num : (13024 : ℕ) ≤ 16384)
  have ht : paperTail256 13024 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13024 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13024 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13024 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13024 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13024 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13022 128 * √(2 / (13024 : ℝ)) *
      (√(13024 : ℝ) + paperT0 13024 + paperTail256 13024) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13024 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13024 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13024 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13022 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13022 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13024 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13024

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13024
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13024 (61 / 100) 165 (17 / (100 * 13024)) (26 / (10 * 13024)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13024 (61 / 100) 165 (17 / (100 * 13024)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (441858641 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (54282389 / 40000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4179120839 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13024 / 13024 * (61 / 100)) ^ 4 * inverseRadius8 (13024 - 1) /
            envelopeGap 13024 (61 / 100) 165 (17 / (100 * 13024)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13024

namespace BstLean.Part266.Row13024
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13024 165 ≤ (4302969421 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13024 165 ≤ (717771711 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (345033413 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13024 165 ≤ (3319831 / 195312500000000000)
  w1 : (tableEnvelope C).w1 13024 165 ≤ (604671067 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13024 165 ≤ (44186269 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (441858641 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (441858641 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (54282389 / 40000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4179120839 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3612869 / 1000000000) : ℝ) ≤ √(17 / (100 * 13024) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13024) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (210204339 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (920957289 / 25000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13024) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13024) ≤ (54292597 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13024) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13024 * (165 : ℝ) ^ 2 + 26 / (10 * 13024) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13024) : ℝ)) (tA 13024 * 165 ^ 2 + 26 / (10 * 13024)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3612869 / 1000000000))) * ((441858641 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3612869 / 1000000000)) ^ 3) * ((54282389 / 40000000000000000000000))) + ((4179120839 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3612869 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13024) : ℝ)) d.D d.V d.P (√(tA 13024) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3612869 / 1000000000)) ^ 2 * (((210204339 / 100000000000000)) * ((920957289 / 25000000000000000)))) + ((4179120839 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13024) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3612869 / 1000000000)) * ((441858641 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13024) : ℝ)) (tA 13024 * 165 ^ 2 + 26 / (10 * 13024)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((441858641 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3612869 / 1000000000)) ^ 2) * ((54282389 / 40000000000000000000000)) + ((4179120839 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13024) : ℝ)) (√(26 / (10 * 13024) : ℝ)) d.D d.V d.P (√(tA 13024) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3612869 / 1000000000)) * (((210204339 / 100000000000000)) * ((920957289 / 25000000000000000))) + ((4179120839 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13024) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((441858641 / 100000000000000000000) : ℝ) + ((4179120839 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13024

namespace BstLean.Part266.Row13024
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13024 165 ∧
    0 ≤ (tableEnvelope C).f1 13024 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13024 165 ∧
    0 ≤ (tableEnvelope C).w1 13024 165 ∧ 0 ≤ (tableEnvelope C).w2 13024 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13024 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13024 165 ∧ 0 ≤ d.f1 13024 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13024 165 ∧ 0 ≤ d.w1 13024 165 ∧ 0 ≤ d.w2 13024 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13024 ≤ 2 * (228 / 100 : ℝ) / 13024 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13024 ≤ 2 * (370 / 100 : ℝ) / 13024 := by
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
    (completeRAData (tableEnvelope C) 13024 165).locationBound 13024 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13024 165).energyBound 13024 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13024 165) (d.f1 13024 165) d.f2 ≤
      32 * (((4302969421 / 1000000000000000000) : ℝ) + (717771711 / 500000000000000000) + (345033413 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13024 165) (d.w1 13024 165)
      (d.w2 13024 165) ≤
      32 * (((3319831 / 195312500000000000) : ℝ) + (604671067 / 50000000000000000000) + (44186269 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13024 165) (d.f1 13024 165) d.f2 ≤
      ((4302969421 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4302969421 / 1000000000000000000)) * ((717771711 / 500000000000000000)) * (126 / 100) +
      2 * (((717771711 / 500000000000000000)) ^ 2 + 2 * ((4302969421 / 1000000000000000000)) * ((345033413 / 1000000000000000000))) +
      6 * ((717771711 / 500000000000000000)) * ((345033413 / 1000000000000000000)) * (126 / 100) + 8 * ((345033413 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13024 165) (d.f1 13024 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13024 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13024 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13024 165) (d.f1 13024 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13024 165) (d.w1 13024 165) (d.w2 13024 165)
  have hwexpr0 : 0 ≤ d.w0 13024 165 + d.w1 13024 165 * √(π / 2) +
      2 * d.w2 13024 165 + energyR16 13024 *
      radiusPolynomialRoot16 (d.w0 13024 165) (d.w1 13024 165) (d.w2 13024 165) := by
    positivity
  constructor
  · change (13024 : ℝ) ^ 8 * (mA 13024 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13024 165) (d.f1 13024 165) d.f2 + locationR16 13024 *
        radiusPolynomialRoot16 (d.f0 13024 165) (d.f1 13024 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13024 : ℝ) ^ 8 * (mA 13024 : ℝ) ^ 8 *
        ((((4302969421 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4302969421 / 1000000000000000000)) * ((717771711 / 500000000000000000)) * (126 / 100) +
          2 * (((717771711 / 500000000000000000)) ^ 2 + 2 * ((4302969421 / 1000000000000000000)) * ((345033413 / 1000000000000000000))) +
          6 * ((717771711 / 500000000000000000)) * ((345033413 / 1000000000000000000)) * (126 / 100) + 8 * ((345033413 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13024) *
          (32 * (((4302969421 / 1000000000000000000) : ℝ) + (717771711 / 500000000000000000) + (345033413 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13024 : ℝ) ^ 16 *
      (d.w0 13024 165 + d.w1 13024 165 * √(π / 2) + 2 * d.w2 13024 165 +
        energyR16 13024 * radiusPolynomialRoot16 (d.w0 13024 165) (d.w1 13024 165)
          (d.w2 13024 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13024 : ℝ) ^ 16 *
        (((3319831 / 195312500000000000) : ℝ) + ((604671067 / 50000000000000000000)) * (126 / 100) + 2 * ((44186269 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13024) *
          (32 * (((3319831 / 195312500000000000) : ℝ) + (604671067 / 50000000000000000000) + (44186269 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13024
