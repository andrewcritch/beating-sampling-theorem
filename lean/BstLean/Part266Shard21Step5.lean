import BstLean.Part266Shard21Step4


/-! A coarse bound on the actual paper statistics constant at dimension 12875. -/
namespace BstLean.Part266.Row12875
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12873 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12873 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12873 128 ≤ (13127 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13127 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12875) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12875 : ℕ))
    (by norm_num : (12875 : ℕ) ≤ 16384)
  have ht : paperTail256 12875 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12875 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12875 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12875 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12875 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12875 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12873 128 * √(2 / (12875 : ℝ)) *
      (√(12875 : ℝ) + paperT0 12875 + paperTail256 12875) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12875 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12875 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12875 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12873 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12873 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12875 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12875

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12875
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12875 (61 / 100) 164 (17 / (100 * 12875)) (26 / (10 * 12875)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12875 (61 / 100) 164 (17 / (100 * 12875)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (228689159 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1420981203 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4584024873 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12875 / 12875 * (61 / 100)) ^ 4 * inverseRadius8 (12875 - 1) /
            envelopeGap 12875 (61 / 100) 164 (17 / (100 * 12875)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12875

namespace BstLean.Part266.Row12875
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12875 164 ≤ (442855503 / 100000000000000000)
  f1 : (tableEnvelope C).f1 12875 164 ≤ (92340049 / 62500000000000000)
  f2 : (tableEnvelope C).f2 ≤ (355103413 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12875 164 ≤ (43986383 / 2500000000000000000)
  w1 : (tableEnvelope C).w1 12875 164 ≤ (1251818791 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12875 164 ≤ (457382759 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (228689159 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (228689159 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1420981203 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4584024873 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1816857 / 500000000) : ℝ) ≤ √(17 / (100 * 12875) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12875) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2138640499 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37695904327 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12875) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12875) ≤ (109841831 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12875) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12875 * (164 : ℝ) ^ 2 + 26 / (10 * 12875) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12875) : ℝ)) (tA 12875 * 164 ^ 2 + 26 / (10 * 12875)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1816857 / 500000000))) * ((228689159 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1816857 / 500000000)) ^ 3) * ((1420981203 / 1000000000000000000000000))) + ((4584024873 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1816857 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12875) : ℝ)) d.D d.V d.P (√(tA 12875) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1816857 / 500000000)) ^ 2 * (((2138640499 / 1000000000000000)) * ((37695904327 / 1000000000000000000)))) + ((4584024873 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12875) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1816857 / 500000000)) * ((228689159 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12875) : ℝ)) (tA 12875 * 164 ^ 2 + 26 / (10 * 12875)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((228689159 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1816857 / 500000000)) ^ 2) * ((1420981203 / 1000000000000000000000000)) + ((4584024873 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12875) : ℝ)) (√(26 / (10 * 12875) : ℝ)) d.D d.V d.P (√(tA 12875) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1816857 / 500000000)) * (((2138640499 / 1000000000000000)) * ((37695904327 / 1000000000000000000))) + ((4584024873 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12875) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((228689159 / 50000000000000000000) : ℝ) + ((4584024873 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12875

namespace BstLean.Part266.Row12875
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12875 164 ∧
    0 ≤ (tableEnvelope C).f1 12875 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12875 164 ∧
    0 ≤ (tableEnvelope C).w1 12875 164 ∧ 0 ≤ (tableEnvelope C).w2 12875 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12875 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12875 164 ∧ 0 ≤ d.f1 12875 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12875 164 ∧ 0 ≤ d.w1 12875 164 ∧ 0 ≤ d.w2 12875 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12875 ≤ 2 * (228 / 100 : ℝ) / 12875 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12875 ≤ 2 * (370 / 100 : ℝ) / 12875 := by
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
    (completeRAData (tableEnvelope C) 12875 164).locationBound 12875 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12875 164).energyBound 12875 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12875 164) (d.f1 12875 164) d.f2 ≤
      32 * (((442855503 / 100000000000000000) : ℝ) + (92340049 / 62500000000000000) + (355103413 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12875 164) (d.w1 12875 164)
      (d.w2 12875 164) ≤
      32 * (((43986383 / 2500000000000000000) : ℝ) + (1251818791 / 100000000000000000000) + (457382759 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12875 164) (d.f1 12875 164) d.f2 ≤
      ((442855503 / 100000000000000000) : ℝ) ^ 2 + 2 * ((442855503 / 100000000000000000)) * ((92340049 / 62500000000000000)) * (126 / 100) +
      2 * (((92340049 / 62500000000000000)) ^ 2 + 2 * ((442855503 / 100000000000000000)) * ((355103413 / 1000000000000000000))) +
      6 * ((92340049 / 62500000000000000)) * ((355103413 / 1000000000000000000)) * (126 / 100) + 8 * ((355103413 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12875 164) (d.f1 12875 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12875 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12875 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12875 164) (d.f1 12875 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12875 164) (d.w1 12875 164) (d.w2 12875 164)
  have hwexpr0 : 0 ≤ d.w0 12875 164 + d.w1 12875 164 * √(π / 2) +
      2 * d.w2 12875 164 + energyR16 12875 *
      radiusPolynomialRoot16 (d.w0 12875 164) (d.w1 12875 164) (d.w2 12875 164) := by
    positivity
  constructor
  · change (12875 : ℝ) ^ 8 * (mA 12875 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12875 164) (d.f1 12875 164) d.f2 + locationR16 12875 *
        radiusPolynomialRoot16 (d.f0 12875 164) (d.f1 12875 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12875 : ℝ) ^ 8 * (mA 12875 : ℝ) ^ 8 *
        ((((442855503 / 100000000000000000) : ℝ) ^ 2 + 2 * ((442855503 / 100000000000000000)) * ((92340049 / 62500000000000000)) * (126 / 100) +
          2 * (((92340049 / 62500000000000000)) ^ 2 + 2 * ((442855503 / 100000000000000000)) * ((355103413 / 1000000000000000000))) +
          6 * ((92340049 / 62500000000000000)) * ((355103413 / 1000000000000000000)) * (126 / 100) + 8 * ((355103413 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12875) *
          (32 * (((442855503 / 100000000000000000) : ℝ) + (92340049 / 62500000000000000) + (355103413 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12875 : ℝ) ^ 16 *
      (d.w0 12875 164 + d.w1 12875 164 * √(π / 2) + 2 * d.w2 12875 164 +
        energyR16 12875 * radiusPolynomialRoot16 (d.w0 12875 164) (d.w1 12875 164)
          (d.w2 12875 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12875 : ℝ) ^ 16 *
        (((43986383 / 2500000000000000000) : ℝ) + ((1251818791 / 100000000000000000000)) * (126 / 100) + 2 * ((457382759 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12875) *
          (32 * (((43986383 / 2500000000000000000) : ℝ) + (1251818791 / 100000000000000000000) + (457382759 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12875

/-! A coarse bound on the actual paper statistics constant at dimension 12876. -/
namespace BstLean.Part266.Row12876
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12874 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12874 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12874 128 ≤ (13128 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13128 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12876) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12876 : ℕ))
    (by norm_num : (12876 : ℕ) ≤ 16384)
  have ht : paperTail256 12876 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12876 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12876 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12876 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12876 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12876 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12874 128 * √(2 / (12876 : ℝ)) *
      (√(12876 : ℝ) + paperT0 12876 + paperTail256 12876) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12876 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12876 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12876 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12874 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12874 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12876 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12876

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12876
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12876 (61 / 100) 164 (17 / (100 * 12876)) (26 / (10 * 12876)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12876 (61 / 100) 164 (17 / (100 * 12876)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (114317939 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (710269901 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (916230047 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12876 / 12876 * (61 / 100)) ^ 4 * inverseRadius8 (12876 - 1) /
            envelopeGap 12876 (61 / 100) 164 (17 / (100 * 12876)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12876

namespace BstLean.Part266.Row12876
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12876 164 ≤ (885538961 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12876 164 ≤ (1477153837 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (44379307 / 125000000000000000)
  w0 : (tableEnvelope C).w0 12876 164 ≤ (439761329 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12876 164 ≤ (1251527099 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12876 164 ≤ (228638097 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (114317939 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (114317939 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (710269901 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (916230047 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3633573 / 1000000000) : ℝ) ≤ √(17 / (100 * 12876) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12876) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2138391349 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4711256139 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12876) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12876) ≤ (1098333 / 10000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12876) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12876 * (164 : ℝ) ^ 2 + 26 / (10 * 12876) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12876) : ℝ)) (tA 12876 * 164 ^ 2 + 26 / (10 * 12876)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3633573 / 1000000000))) * ((114317939 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3633573 / 1000000000)) ^ 3) * ((710269901 / 500000000000000000000000))) + ((916230047 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3633573 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12876) : ℝ)) d.D d.V d.P (√(tA 12876) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3633573 / 1000000000)) ^ 2 * (((2138391349 / 1000000000000000)) * ((4711256139 / 125000000000000000)))) + ((916230047 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12876) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3633573 / 1000000000)) * ((114317939 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12876) : ℝ)) (tA 12876 * 164 ^ 2 + 26 / (10 * 12876)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((114317939 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3633573 / 1000000000)) ^ 2) * ((710269901 / 500000000000000000000000)) + ((916230047 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12876) : ℝ)) (√(26 / (10 * 12876) : ℝ)) d.D d.V d.P (√(tA 12876) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3633573 / 1000000000)) * (((2138391349 / 1000000000000000)) * ((4711256139 / 125000000000000000))) + ((916230047 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12876) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((114317939 / 25000000000000000000) : ℝ) + ((916230047 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12876

namespace BstLean.Part266.Row12876
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12876 164 ∧
    0 ≤ (tableEnvelope C).f1 12876 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12876 164 ∧
    0 ≤ (tableEnvelope C).w1 12876 164 ∧ 0 ≤ (tableEnvelope C).w2 12876 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12876 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12876 164 ∧ 0 ≤ d.f1 12876 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12876 164 ∧ 0 ≤ d.w1 12876 164 ∧ 0 ≤ d.w2 12876 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12876 ≤ 2 * (228 / 100 : ℝ) / 12876 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12876 ≤ 2 * (370 / 100 : ℝ) / 12876 := by
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
    (completeRAData (tableEnvelope C) 12876 164).locationBound 12876 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12876 164).energyBound 12876 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12876 164) (d.f1 12876 164) d.f2 ≤
      32 * (((885538961 / 200000000000000000) : ℝ) + (1477153837 / 1000000000000000000) + (44379307 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12876 164) (d.w1 12876 164)
      (d.w2 12876 164) ≤
      32 * (((439761329 / 25000000000000000000) : ℝ) + (1251527099 / 100000000000000000000) + (228638097 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12876 164) (d.f1 12876 164) d.f2 ≤
      ((885538961 / 200000000000000000) : ℝ) ^ 2 + 2 * ((885538961 / 200000000000000000)) * ((1477153837 / 1000000000000000000)) * (126 / 100) +
      2 * (((1477153837 / 1000000000000000000)) ^ 2 + 2 * ((885538961 / 200000000000000000)) * ((44379307 / 125000000000000000))) +
      6 * ((1477153837 / 1000000000000000000)) * ((44379307 / 125000000000000000)) * (126 / 100) + 8 * ((44379307 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12876 164) (d.f1 12876 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12876 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12876 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12876 164) (d.f1 12876 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12876 164) (d.w1 12876 164) (d.w2 12876 164)
  have hwexpr0 : 0 ≤ d.w0 12876 164 + d.w1 12876 164 * √(π / 2) +
      2 * d.w2 12876 164 + energyR16 12876 *
      radiusPolynomialRoot16 (d.w0 12876 164) (d.w1 12876 164) (d.w2 12876 164) := by
    positivity
  constructor
  · change (12876 : ℝ) ^ 8 * (mA 12876 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12876 164) (d.f1 12876 164) d.f2 + locationR16 12876 *
        radiusPolynomialRoot16 (d.f0 12876 164) (d.f1 12876 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12876 : ℝ) ^ 8 * (mA 12876 : ℝ) ^ 8 *
        ((((885538961 / 200000000000000000) : ℝ) ^ 2 + 2 * ((885538961 / 200000000000000000)) * ((1477153837 / 1000000000000000000)) * (126 / 100) +
          2 * (((1477153837 / 1000000000000000000)) ^ 2 + 2 * ((885538961 / 200000000000000000)) * ((44379307 / 125000000000000000))) +
          6 * ((1477153837 / 1000000000000000000)) * ((44379307 / 125000000000000000)) * (126 / 100) + 8 * ((44379307 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12876) *
          (32 * (((885538961 / 200000000000000000) : ℝ) + (1477153837 / 1000000000000000000) + (44379307 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12876 : ℝ) ^ 16 *
      (d.w0 12876 164 + d.w1 12876 164 * √(π / 2) + 2 * d.w2 12876 164 +
        energyR16 12876 * radiusPolynomialRoot16 (d.w0 12876 164) (d.w1 12876 164)
          (d.w2 12876 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12876 : ℝ) ^ 16 *
        (((439761329 / 25000000000000000000) : ℝ) + ((1251527099 / 100000000000000000000)) * (126 / 100) + 2 * ((228638097 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12876) *
          (32 * (((439761329 / 25000000000000000000) : ℝ) + (1251527099 / 100000000000000000000) + (228638097 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12876

/-! A coarse bound on the actual paper statistics constant at dimension 12877. -/
namespace BstLean.Part266.Row12877
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12875 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12875 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12875 128 ≤ (13129 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13129 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12877) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12877 : ℕ))
    (by norm_num : (12877 : ℕ) ≤ 16384)
  have ht : paperTail256 12877 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12877 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12877 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12877 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12877 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12877 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12875 128 * √(2 / (12877 : ℝ)) *
      (√(12877 : ℝ) + paperT0 12877 + paperTail256 12877) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12877 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12877 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12877 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12875 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12875 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12877 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12877

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12877
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12877 (61 / 100) 164 (17 / (100 * 12877)) (26 / (10 * 12877)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12877 (61 / 100) 164 (17 / (100 * 12877)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (228582613 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (355024643 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4578277627 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12877 / 12877 * (61 / 100)) ^ 4 * inverseRadius8 (12877 - 1) /
            envelopeGap 12877 (61 / 100) 164 (17 / (100 * 12877)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12877

namespace BstLean.Part266.Row12877
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12877 164 ≤ (4426834869 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12877 164 ≤ (73843349 / 50000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (354965519 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12877 164 ≤ (35172709 / 2000000000000000000)
  w1 : (tableEnvelope C).w1 12877 164 ≤ (625617751 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12877 164 ≤ (457169661 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (228582613 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (228582613 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (355024643 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4578277627 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((454179 / 125000000) : ℝ) ≤ √(17 / (100 * 12877) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12877) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1069071123 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7536839051 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12877) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12877) ≤ (10982477 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12877) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12877 * (164 : ℝ) ^ 2 + 26 / (10 * 12877) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12877) : ℝ)) (tA 12877 * 164 ^ 2 + 26 / (10 * 12877)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((454179 / 125000000))) * ((228582613 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((454179 / 125000000)) ^ 3) * ((355024643 / 250000000000000000000000))) + ((4578277627 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((454179 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12877) : ℝ)) d.D d.V d.P (√(tA 12877) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((454179 / 125000000)) ^ 2 * (((1069071123 / 500000000000000)) * ((7536839051 / 200000000000000000)))) + ((4578277627 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12877) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((454179 / 125000000)) * ((228582613 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12877) : ℝ)) (tA 12877 * 164 ^ 2 + 26 / (10 * 12877)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((228582613 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((454179 / 125000000)) ^ 2) * ((355024643 / 250000000000000000000000)) + ((4578277627 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12877) : ℝ)) (√(26 / (10 * 12877) : ℝ)) d.D d.V d.P (√(tA 12877) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((454179 / 125000000)) * (((1069071123 / 500000000000000)) * ((7536839051 / 200000000000000000))) + ((4578277627 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12877) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((228582613 / 50000000000000000000) : ℝ) + ((4578277627 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12877

namespace BstLean.Part266.Row12877
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12877 164 ∧
    0 ≤ (tableEnvelope C).f1 12877 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12877 164 ∧
    0 ≤ (tableEnvelope C).w1 12877 164 ∧ 0 ≤ (tableEnvelope C).w2 12877 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12877 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12877 164 ∧ 0 ≤ d.f1 12877 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12877 164 ∧ 0 ≤ d.w1 12877 164 ∧ 0 ≤ d.w2 12877 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12877 ≤ 2 * (228 / 100 : ℝ) / 12877 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12877 ≤ 2 * (370 / 100 : ℝ) / 12877 := by
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
    (completeRAData (tableEnvelope C) 12877 164).locationBound 12877 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12877 164).energyBound 12877 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12877 164) (d.f1 12877 164) d.f2 ≤
      32 * (((4426834869 / 1000000000000000000) : ℝ) + (73843349 / 50000000000000000) + (354965519 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12877 164) (d.w1 12877 164)
      (d.w2 12877 164) ≤
      32 * (((35172709 / 2000000000000000000) : ℝ) + (625617751 / 50000000000000000000) + (457169661 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12877 164) (d.f1 12877 164) d.f2 ≤
      ((4426834869 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4426834869 / 1000000000000000000)) * ((73843349 / 50000000000000000)) * (126 / 100) +
      2 * (((73843349 / 50000000000000000)) ^ 2 + 2 * ((4426834869 / 1000000000000000000)) * ((354965519 / 1000000000000000000))) +
      6 * ((73843349 / 50000000000000000)) * ((354965519 / 1000000000000000000)) * (126 / 100) + 8 * ((354965519 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12877 164) (d.f1 12877 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12877 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12877 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12877 164) (d.f1 12877 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12877 164) (d.w1 12877 164) (d.w2 12877 164)
  have hwexpr0 : 0 ≤ d.w0 12877 164 + d.w1 12877 164 * √(π / 2) +
      2 * d.w2 12877 164 + energyR16 12877 *
      radiusPolynomialRoot16 (d.w0 12877 164) (d.w1 12877 164) (d.w2 12877 164) := by
    positivity
  constructor
  · change (12877 : ℝ) ^ 8 * (mA 12877 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12877 164) (d.f1 12877 164) d.f2 + locationR16 12877 *
        radiusPolynomialRoot16 (d.f0 12877 164) (d.f1 12877 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12877 : ℝ) ^ 8 * (mA 12877 : ℝ) ^ 8 *
        ((((4426834869 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4426834869 / 1000000000000000000)) * ((73843349 / 50000000000000000)) * (126 / 100) +
          2 * (((73843349 / 50000000000000000)) ^ 2 + 2 * ((4426834869 / 1000000000000000000)) * ((354965519 / 1000000000000000000))) +
          6 * ((73843349 / 50000000000000000)) * ((354965519 / 1000000000000000000)) * (126 / 100) + 8 * ((354965519 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12877) *
          (32 * (((4426834869 / 1000000000000000000) : ℝ) + (73843349 / 50000000000000000) + (354965519 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12877 : ℝ) ^ 16 *
      (d.w0 12877 164 + d.w1 12877 164 * √(π / 2) + 2 * d.w2 12877 164 +
        energyR16 12877 * radiusPolynomialRoot16 (d.w0 12877 164) (d.w1 12877 164)
          (d.w2 12877 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12877 : ℝ) ^ 16 *
        (((35172709 / 2000000000000000000) : ℝ) + ((625617751 / 50000000000000000000)) * (126 / 100) + 2 * ((457169661 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12877) *
          (32 * (((35172709 / 2000000000000000000) : ℝ) + (625617751 / 50000000000000000000) + (457169661 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12877

/-! A coarse bound on the actual paper statistics constant at dimension 12878. -/
namespace BstLean.Part266.Row12878
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12876 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12876 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12876 128 ≤ (13130 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13130 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12878) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12878 : ℕ))
    (by norm_num : (12878 : ℕ) ≤ 16384)
  have ht : paperTail256 12878 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12878 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12878 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12878 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12878 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12878 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12876 128 * √(2 / (12878 : ℝ)) *
      (√(12878 : ℝ) + paperT0 12878 + paperTail256 12878) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12878 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12878 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12878 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12876 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12876 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12878 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12878

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12878
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12878 (61 / 100) 164 (17 / (100 * 12878)) (26 / (10 * 12878)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12878 (61 / 100) 164 (17 / (100 * 12878)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (45705873 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1419657513 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (571925881 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12878 / 12878 * (61 / 100)) ^ 4 * inverseRadius8 (12878 - 1) /
            envelopeGap 12878 (61 / 100) 164 (17 / (100 * 12878)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12878

namespace BstLean.Part266.Row12878
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12878 164 ≤ (177039009 / 40000000000000000)
  f1 : (tableEnvelope C).f1 12878 164 ≤ (295316043 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (177448301 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12878 164 ≤ (1758225723 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12878 164 ≤ (1250944001 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12878 164 ≤ (457063163 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (45705873 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (45705873 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1419657513 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (571925881 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3633291 / 1000000000) : ℝ) ≤ √(17 / (100 * 12878) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12878) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (267236649 / 125000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37678342759 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12878) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12878) ≤ (54908121 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12878) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12878 * (164 : ℝ) ^ 2 + 26 / (10 * 12878) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12878) : ℝ)) (tA 12878 * 164 ^ 2 + 26 / (10 * 12878)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3633291 / 1000000000))) * ((45705873 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3633291 / 1000000000)) ^ 3) * ((1419657513 / 1000000000000000000000000))) + ((571925881 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3633291 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12878) : ℝ)) d.D d.V d.P (√(tA 12878) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3633291 / 1000000000)) ^ 2 * (((267236649 / 125000000000000)) * ((37678342759 / 1000000000000000000)))) + ((571925881 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12878) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3633291 / 1000000000)) * ((45705873 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12878) : ℝ)) (tA 12878 * 164 ^ 2 + 26 / (10 * 12878)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((45705873 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3633291 / 1000000000)) ^ 2) * ((1419657513 / 1000000000000000000000000)) + ((571925881 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12878) : ℝ)) (√(26 / (10 * 12878) : ℝ)) d.D d.V d.P (√(tA 12878) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3633291 / 1000000000)) * (((267236649 / 125000000000000)) * ((37678342759 / 1000000000000000000))) + ((571925881 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12878) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((45705873 / 10000000000000000000) : ℝ) + ((571925881 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12878

namespace BstLean.Part266.Row12878
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12878 164 ∧
    0 ≤ (tableEnvelope C).f1 12878 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12878 164 ∧
    0 ≤ (tableEnvelope C).w1 12878 164 ∧ 0 ≤ (tableEnvelope C).w2 12878 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12878 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12878 164 ∧ 0 ≤ d.f1 12878 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12878 164 ∧ 0 ≤ d.w1 12878 164 ∧ 0 ≤ d.w2 12878 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12878 ≤ 2 * (228 / 100 : ℝ) / 12878 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12878 ≤ 2 * (370 / 100 : ℝ) / 12878 := by
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
    (completeRAData (tableEnvelope C) 12878 164).locationBound 12878 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12878 164).energyBound 12878 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12878 164) (d.f1 12878 164) d.f2 ≤
      32 * (((177039009 / 40000000000000000) : ℝ) + (295316043 / 200000000000000000) + (177448301 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12878 164) (d.w1 12878 164)
      (d.w2 12878 164) ≤
      32 * (((1758225723 / 100000000000000000000) : ℝ) + (1250944001 / 100000000000000000000) + (457063163 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12878 164) (d.f1 12878 164) d.f2 ≤
      ((177039009 / 40000000000000000) : ℝ) ^ 2 + 2 * ((177039009 / 40000000000000000)) * ((295316043 / 200000000000000000)) * (126 / 100) +
      2 * (((295316043 / 200000000000000000)) ^ 2 + 2 * ((177039009 / 40000000000000000)) * ((177448301 / 500000000000000000))) +
      6 * ((295316043 / 200000000000000000)) * ((177448301 / 500000000000000000)) * (126 / 100) + 8 * ((177448301 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12878 164) (d.f1 12878 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12878 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12878 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12878 164) (d.f1 12878 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12878 164) (d.w1 12878 164) (d.w2 12878 164)
  have hwexpr0 : 0 ≤ d.w0 12878 164 + d.w1 12878 164 * √(π / 2) +
      2 * d.w2 12878 164 + energyR16 12878 *
      radiusPolynomialRoot16 (d.w0 12878 164) (d.w1 12878 164) (d.w2 12878 164) := by
    positivity
  constructor
  · change (12878 : ℝ) ^ 8 * (mA 12878 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12878 164) (d.f1 12878 164) d.f2 + locationR16 12878 *
        radiusPolynomialRoot16 (d.f0 12878 164) (d.f1 12878 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12878 : ℝ) ^ 8 * (mA 12878 : ℝ) ^ 8 *
        ((((177039009 / 40000000000000000) : ℝ) ^ 2 + 2 * ((177039009 / 40000000000000000)) * ((295316043 / 200000000000000000)) * (126 / 100) +
          2 * (((295316043 / 200000000000000000)) ^ 2 + 2 * ((177039009 / 40000000000000000)) * ((177448301 / 500000000000000000))) +
          6 * ((295316043 / 200000000000000000)) * ((177448301 / 500000000000000000)) * (126 / 100) + 8 * ((177448301 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12878) *
          (32 * (((177039009 / 40000000000000000) : ℝ) + (295316043 / 200000000000000000) + (177448301 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12878 : ℝ) ^ 16 *
      (d.w0 12878 164 + d.w1 12878 164 * √(π / 2) + 2 * d.w2 12878 164 +
        energyR16 12878 * radiusPolynomialRoot16 (d.w0 12878 164) (d.w1 12878 164)
          (d.w2 12878 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12878 : ℝ) ^ 16 *
        (((1758225723 / 100000000000000000000) : ℝ) + ((1250944001 / 100000000000000000000)) * (126 / 100) + 2 * ((457063163 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12878) *
          (32 * (((1758225723 / 100000000000000000000) : ℝ) + (1250944001 / 100000000000000000000) + (457063163 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12878

/-! A coarse bound on the actual paper statistics constant at dimension 12879. -/
namespace BstLean.Part266.Row12879
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12877 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12877 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12877 128 ≤ (13131 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13131 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12879) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12879 : ℕ))
    (by norm_num : (12879 : ℕ) ≤ 16384)
  have ht : paperTail256 12879 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12879 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12879 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12879 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12879 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12879 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12877 128 * √(2 / (12879 : ℝ)) *
      (√(12879 : ℝ) + paperT0 12879 + paperTail256 12879) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12879 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12879 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12879 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12877 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12877 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12879 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12879

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12879
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12879 (61 / 100) 164 (17 / (100 * 12879)) (26 / (10 * 12879)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12879 (61 / 100) 164 (17 / (100 * 12879)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (456952267 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (709608313 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (914507699 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12879 / 12879 * (61 / 100)) ^ 4 * inverseRadius8 (12879 - 1) /
            envelopeGap 12879 (61 / 100) 164 (17 / (100 * 12879)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12879

namespace BstLean.Part266.Row12879
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12879 164 ≤ (35400927 / 8000000000000000)
  f1 : (tableEnvelope C).f1 12879 164 ≤ (738146771 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (177413853 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12879 164 ≤ (219727017 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 12879 164 ≤ (1250652597 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12879 164 ≤ (456956697 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (456952267 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (456952267 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (709608313 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (914507699 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((72663 / 20000000) : ℝ) ≤ √(17 / (100 * 12879) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12879) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2137644187 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9418122909 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12879) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12879) ≤ (27451929 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12879) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12879 * (164 : ℝ) ^ 2 + 26 / (10 * 12879) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12879) : ℝ)) (tA 12879 * 164 ^ 2 + 26 / (10 * 12879)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((72663 / 20000000))) * ((456952267 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((72663 / 20000000)) ^ 3) * ((709608313 / 500000000000000000000000))) + ((914507699 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((72663 / 20000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12879) : ℝ)) d.D d.V d.P (√(tA 12879) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((72663 / 20000000)) ^ 2 * (((2137644187 / 1000000000000000)) * ((9418122909 / 250000000000000000)))) + ((914507699 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12879) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((72663 / 20000000)) * ((456952267 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12879) : ℝ)) (tA 12879 * 164 ^ 2 + 26 / (10 * 12879)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((456952267 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((72663 / 20000000)) ^ 2) * ((709608313 / 500000000000000000000000)) + ((914507699 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12879) : ℝ)) (√(26 / (10 * 12879) : ℝ)) d.D d.V d.P (√(tA 12879) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((72663 / 20000000)) * (((2137644187 / 1000000000000000)) * ((9418122909 / 250000000000000000))) + ((914507699 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12879) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((456952267 / 100000000000000000000) : ℝ) + ((914507699 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12879

namespace BstLean.Part266.Row12879
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12879 164 ∧
    0 ≤ (tableEnvelope C).f1 12879 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12879 164 ∧
    0 ≤ (tableEnvelope C).w1 12879 164 ∧ 0 ≤ (tableEnvelope C).w2 12879 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12879 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12879 164 ∧ 0 ≤ d.f1 12879 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12879 164 ∧ 0 ≤ d.w1 12879 164 ∧ 0 ≤ d.w2 12879 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12879 ≤ 2 * (228 / 100 : ℝ) / 12879 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12879 ≤ 2 * (370 / 100 : ℝ) / 12879 := by
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
    (completeRAData (tableEnvelope C) 12879 164).locationBound 12879 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12879 164).energyBound 12879 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12879 164) (d.f1 12879 164) d.f2 ≤
      32 * (((35400927 / 8000000000000000) : ℝ) + (738146771 / 500000000000000000) + (177413853 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12879 164) (d.w1 12879 164)
      (d.w2 12879 164) ≤
      32 * (((219727017 / 12500000000000000000) : ℝ) + (1250652597 / 100000000000000000000) + (456956697 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12879 164) (d.f1 12879 164) d.f2 ≤
      ((35400927 / 8000000000000000) : ℝ) ^ 2 + 2 * ((35400927 / 8000000000000000)) * ((738146771 / 500000000000000000)) * (126 / 100) +
      2 * (((738146771 / 500000000000000000)) ^ 2 + 2 * ((35400927 / 8000000000000000)) * ((177413853 / 500000000000000000))) +
      6 * ((738146771 / 500000000000000000)) * ((177413853 / 500000000000000000)) * (126 / 100) + 8 * ((177413853 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12879 164) (d.f1 12879 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12879 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12879 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12879 164) (d.f1 12879 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12879 164) (d.w1 12879 164) (d.w2 12879 164)
  have hwexpr0 : 0 ≤ d.w0 12879 164 + d.w1 12879 164 * √(π / 2) +
      2 * d.w2 12879 164 + energyR16 12879 *
      radiusPolynomialRoot16 (d.w0 12879 164) (d.w1 12879 164) (d.w2 12879 164) := by
    positivity
  constructor
  · change (12879 : ℝ) ^ 8 * (mA 12879 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12879 164) (d.f1 12879 164) d.f2 + locationR16 12879 *
        radiusPolynomialRoot16 (d.f0 12879 164) (d.f1 12879 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12879 : ℝ) ^ 8 * (mA 12879 : ℝ) ^ 8 *
        ((((35400927 / 8000000000000000) : ℝ) ^ 2 + 2 * ((35400927 / 8000000000000000)) * ((738146771 / 500000000000000000)) * (126 / 100) +
          2 * (((738146771 / 500000000000000000)) ^ 2 + 2 * ((35400927 / 8000000000000000)) * ((177413853 / 500000000000000000))) +
          6 * ((738146771 / 500000000000000000)) * ((177413853 / 500000000000000000)) * (126 / 100) + 8 * ((177413853 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12879) *
          (32 * (((35400927 / 8000000000000000) : ℝ) + (738146771 / 500000000000000000) + (177413853 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12879 : ℝ) ^ 16 *
      (d.w0 12879 164 + d.w1 12879 164 * √(π / 2) + 2 * d.w2 12879 164 +
        energyR16 12879 * radiusPolynomialRoot16 (d.w0 12879 164) (d.w1 12879 164)
          (d.w2 12879 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12879 : ℝ) ^ 16 *
        (((219727017 / 12500000000000000000) : ℝ) + ((1250652597 / 100000000000000000000)) * (126 / 100) + 2 * ((456956697 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12879) *
          (32 * (((219727017 / 12500000000000000000) : ℝ) + (1250652597 / 100000000000000000000) + (456956697 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12879

/-! A coarse bound on the actual paper statistics constant at dimension 12880. -/
namespace BstLean.Part266.Row12880
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12878 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12878 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12878 128 ≤ (13132 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13132 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12880) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12880 : ℕ))
    (by norm_num : (12880 : ℕ) ≤ 16384)
  have ht : paperTail256 12880 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12880 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12880 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12880 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12880 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12880 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12878 128 * √(2 / (12880 : ℝ)) *
      (√(12880 : ℝ) + paperT0 12880 + paperTail256 12880) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12880 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12880 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12880 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12878 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12878 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12880 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12880

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12880
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12880 (61 / 100) 164 (17 / (100 * 12880)) (26 / (10 * 12880)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12880 (61 / 100) 164 (17 / (100 * 12880)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (456845837 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (141877591 / 100000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4569671967 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12880 / 12880 * (61 / 100)) ^ 4 * inverseRadius8 (12880 - 1) /
            envelopeGap 12880 (61 / 100) 164 (17 / (100 * 12880)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12880

namespace BstLean.Part266.Row12880
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12880 164 ≤ (276516051 / 62500000000000000)
  f1 : (tableEnvelope C).f1 12880 164 ≤ (18450087 / 12500000000000000)
  f2 : (tableEnvelope C).f2 ≤ (35475883 / 100000000000000000)
  w0 : (tableEnvelope C).w0 12880 164 ≤ (54918959 / 3125000000000000000)
  w1 : (tableEnvelope C).w1 12880 164 ≤ (125036129 / 10000000000000000000)
  w2 : (tableEnvelope C).w2 12880 164 ≤ (57106283 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (456845837 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (456845837 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (141877591 / 100000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4569671967 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3633009 / 1000000000) : ℝ) ≤ √(17 / (100 * 12880) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12880) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2137395231 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18833320937 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12880) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12880) ≤ (10979919 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12880) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12880 * (164 : ℝ) ^ 2 + 26 / (10 * 12880) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12880) : ℝ)) (tA 12880 * 164 ^ 2 + 26 / (10 * 12880)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3633009 / 1000000000))) * ((456845837 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3633009 / 1000000000)) ^ 3) * ((141877591 / 100000000000000000000000))) + ((4569671967 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3633009 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12880) : ℝ)) d.D d.V d.P (√(tA 12880) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3633009 / 1000000000)) ^ 2 * (((2137395231 / 1000000000000000)) * ((18833320937 / 500000000000000000)))) + ((4569671967 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12880) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3633009 / 1000000000)) * ((456845837 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12880) : ℝ)) (tA 12880 * 164 ^ 2 + 26 / (10 * 12880)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((456845837 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3633009 / 1000000000)) ^ 2) * ((141877591 / 100000000000000000000000)) + ((4569671967 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12880) : ℝ)) (√(26 / (10 * 12880) : ℝ)) d.D d.V d.P (√(tA 12880) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3633009 / 1000000000)) * (((2137395231 / 1000000000000000)) * ((18833320937 / 500000000000000000))) + ((4569671967 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12880) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((456845837 / 100000000000000000000) : ℝ) + ((4569671967 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12880

namespace BstLean.Part266.Row12880
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12880 164 ∧
    0 ≤ (tableEnvelope C).f1 12880 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12880 164 ∧
    0 ≤ (tableEnvelope C).w1 12880 164 ∧ 0 ≤ (tableEnvelope C).w2 12880 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12880 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12880 164 ∧ 0 ≤ d.f1 12880 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12880 164 ∧ 0 ≤ d.w1 12880 164 ∧ 0 ≤ d.w2 12880 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12880 ≤ 2 * (228 / 100 : ℝ) / 12880 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12880 ≤ 2 * (370 / 100 : ℝ) / 12880 := by
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
    (completeRAData (tableEnvelope C) 12880 164).locationBound 12880 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12880 164).energyBound 12880 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12880 164) (d.f1 12880 164) d.f2 ≤
      32 * (((276516051 / 62500000000000000) : ℝ) + (18450087 / 12500000000000000) + (35475883 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12880 164) (d.w1 12880 164)
      (d.w2 12880 164) ≤
      32 * (((54918959 / 3125000000000000000) : ℝ) + (125036129 / 10000000000000000000) + (57106283 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12880 164) (d.f1 12880 164) d.f2 ≤
      ((276516051 / 62500000000000000) : ℝ) ^ 2 + 2 * ((276516051 / 62500000000000000)) * ((18450087 / 12500000000000000)) * (126 / 100) +
      2 * (((18450087 / 12500000000000000)) ^ 2 + 2 * ((276516051 / 62500000000000000)) * ((35475883 / 100000000000000000))) +
      6 * ((18450087 / 12500000000000000)) * ((35475883 / 100000000000000000)) * (126 / 100) + 8 * ((35475883 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12880 164) (d.f1 12880 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12880 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12880 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12880 164) (d.f1 12880 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12880 164) (d.w1 12880 164) (d.w2 12880 164)
  have hwexpr0 : 0 ≤ d.w0 12880 164 + d.w1 12880 164 * √(π / 2) +
      2 * d.w2 12880 164 + energyR16 12880 *
      radiusPolynomialRoot16 (d.w0 12880 164) (d.w1 12880 164) (d.w2 12880 164) := by
    positivity
  constructor
  · change (12880 : ℝ) ^ 8 * (mA 12880 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12880 164) (d.f1 12880 164) d.f2 + locationR16 12880 *
        radiusPolynomialRoot16 (d.f0 12880 164) (d.f1 12880 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12880 : ℝ) ^ 8 * (mA 12880 : ℝ) ^ 8 *
        ((((276516051 / 62500000000000000) : ℝ) ^ 2 + 2 * ((276516051 / 62500000000000000)) * ((18450087 / 12500000000000000)) * (126 / 100) +
          2 * (((18450087 / 12500000000000000)) ^ 2 + 2 * ((276516051 / 62500000000000000)) * ((35475883 / 100000000000000000))) +
          6 * ((18450087 / 12500000000000000)) * ((35475883 / 100000000000000000)) * (126 / 100) + 8 * ((35475883 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12880) *
          (32 * (((276516051 / 62500000000000000) : ℝ) + (18450087 / 12500000000000000) + (35475883 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12880 : ℝ) ^ 16 *
      (d.w0 12880 164 + d.w1 12880 164 * √(π / 2) + 2 * d.w2 12880 164 +
        energyR16 12880 * radiusPolynomialRoot16 (d.w0 12880 164) (d.w1 12880 164)
          (d.w2 12880 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12880 : ℝ) ^ 16 *
        (((54918959 / 3125000000000000000) : ℝ) + ((125036129 / 10000000000000000000)) * (126 / 100) + 2 * ((57106283 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12880) *
          (32 * (((54918959 / 3125000000000000000) : ℝ) + (125036129 / 10000000000000000000) + (57106283 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12880

/-! A coarse bound on the actual paper statistics constant at dimension 12881. -/
namespace BstLean.Part266.Row12881
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12879 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12879 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12879 128 ≤ (13133 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13133 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12881) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12881 : ℕ))
    (by norm_num : (12881 : ℕ) ≤ 16384)
  have ht : paperTail256 12881 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12881 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12881 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12881 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12881 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12881 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12879 128 * √(2 / (12881 : ℝ)) *
      (√(12881 : ℝ) + paperT0 12881 + paperTail256 12881) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12881 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12881 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12881 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12879 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12879 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12881 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12881

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12881
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12881 (61 / 100) 164 (17 / (100 * 12881)) (26 / (10 * 12881)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12881 (61 / 100) 164 (17 / (100 * 12881)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (456739439 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (354583841 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4566807463 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12881 / 12881 * (61 / 100)) ^ 4 * inverseRadius8 (12881 - 1) /
            envelopeGap 12881 (61 / 100) 164 (17 / (100 * 12881)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12881

namespace BstLean.Part266.Row12881
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12881 164 ≤ (1105849511 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12881 164 ≤ (1475720467 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (354689973 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12881 164 ≤ (1756997377 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12881 164 ≤ (1250070077 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12881 164 ≤ (456743863 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (456739439 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (456739439 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (354583841 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4566807463 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((908217 / 250000000) : ℝ) ≤ √(17 / (100 * 12881) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12881) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (26714329 / 12500000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1883039673 / 50000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12881) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12881) ≤ (54895333 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12881) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12881 * (164 : ℝ) ^ 2 + 26 / (10 * 12881) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12881) : ℝ)) (tA 12881 * 164 ^ 2 + 26 / (10 * 12881)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((908217 / 250000000))) * ((456739439 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((908217 / 250000000)) ^ 3) * ((354583841 / 250000000000000000000000))) + ((4566807463 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((908217 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12881) : ℝ)) d.D d.V d.P (√(tA 12881) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((908217 / 250000000)) ^ 2 * (((26714329 / 12500000000000)) * ((1883039673 / 50000000000000000)))) + ((4566807463 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12881) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((908217 / 250000000)) * ((456739439 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12881) : ℝ)) (tA 12881 * 164 ^ 2 + 26 / (10 * 12881)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((456739439 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((908217 / 250000000)) ^ 2) * ((354583841 / 250000000000000000000000)) + ((4566807463 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12881) : ℝ)) (√(26 / (10 * 12881) : ℝ)) d.D d.V d.P (√(tA 12881) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((908217 / 250000000)) * (((26714329 / 12500000000000)) * ((1883039673 / 50000000000000000))) + ((4566807463 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12881) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((456739439 / 100000000000000000000) : ℝ) + ((4566807463 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12881

namespace BstLean.Part266.Row12881
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12881 164 ∧
    0 ≤ (tableEnvelope C).f1 12881 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12881 164 ∧
    0 ≤ (tableEnvelope C).w1 12881 164 ∧ 0 ≤ (tableEnvelope C).w2 12881 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12881 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12881 164 ∧ 0 ≤ d.f1 12881 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12881 164 ∧ 0 ≤ d.w1 12881 164 ∧ 0 ≤ d.w2 12881 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12881 ≤ 2 * (228 / 100 : ℝ) / 12881 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12881 ≤ 2 * (370 / 100 : ℝ) / 12881 := by
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
    (completeRAData (tableEnvelope C) 12881 164).locationBound 12881 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12881 164).energyBound 12881 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12881 164) (d.f1 12881 164) d.f2 ≤
      32 * (((1105849511 / 250000000000000000) : ℝ) + (1475720467 / 1000000000000000000) + (354689973 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12881 164) (d.w1 12881 164)
      (d.w2 12881 164) ≤
      32 * (((1756997377 / 100000000000000000000) : ℝ) + (1250070077 / 100000000000000000000) + (456743863 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12881 164) (d.f1 12881 164) d.f2 ≤
      ((1105849511 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1105849511 / 250000000000000000)) * ((1475720467 / 1000000000000000000)) * (126 / 100) +
      2 * (((1475720467 / 1000000000000000000)) ^ 2 + 2 * ((1105849511 / 250000000000000000)) * ((354689973 / 1000000000000000000))) +
      6 * ((1475720467 / 1000000000000000000)) * ((354689973 / 1000000000000000000)) * (126 / 100) + 8 * ((354689973 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12881 164) (d.f1 12881 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12881 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12881 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12881 164) (d.f1 12881 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12881 164) (d.w1 12881 164) (d.w2 12881 164)
  have hwexpr0 : 0 ≤ d.w0 12881 164 + d.w1 12881 164 * √(π / 2) +
      2 * d.w2 12881 164 + energyR16 12881 *
      radiusPolynomialRoot16 (d.w0 12881 164) (d.w1 12881 164) (d.w2 12881 164) := by
    positivity
  constructor
  · change (12881 : ℝ) ^ 8 * (mA 12881 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12881 164) (d.f1 12881 164) d.f2 + locationR16 12881 *
        radiusPolynomialRoot16 (d.f0 12881 164) (d.f1 12881 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12881 : ℝ) ^ 8 * (mA 12881 : ℝ) ^ 8 *
        ((((1105849511 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1105849511 / 250000000000000000)) * ((1475720467 / 1000000000000000000)) * (126 / 100) +
          2 * (((1475720467 / 1000000000000000000)) ^ 2 + 2 * ((1105849511 / 250000000000000000)) * ((354689973 / 1000000000000000000))) +
          6 * ((1475720467 / 1000000000000000000)) * ((354689973 / 1000000000000000000)) * (126 / 100) + 8 * ((354689973 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12881) *
          (32 * (((1105849511 / 250000000000000000) : ℝ) + (1475720467 / 1000000000000000000) + (354689973 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12881 : ℝ) ^ 16 *
      (d.w0 12881 164 + d.w1 12881 164 * √(π / 2) + 2 * d.w2 12881 164 +
        energyR16 12881 * radiusPolynomialRoot16 (d.w0 12881 164) (d.w1 12881 164)
          (d.w2 12881 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12881 : ℝ) ^ 16 *
        (((1756997377 / 100000000000000000000) : ℝ) + ((1250070077 / 100000000000000000000)) * (126 / 100) + 2 * ((456743863 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12881) *
          (32 * (((1756997377 / 100000000000000000000) : ℝ) + (1250070077 / 100000000000000000000) + (456743863 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12881

/-! A coarse bound on the actual paper statistics constant at dimension 12882. -/
namespace BstLean.Part266.Row12882
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12880 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12880 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12880 128 ≤ (13134 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13134 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12882) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12882 : ℕ))
    (by norm_num : (12882 : ℕ) ≤ 16384)
  have ht : paperTail256 12882 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12882 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12882 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12882 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12882 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12882 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12880 128 * √(2 / (12882 : ℝ)) *
      (√(12882 : ℝ) + paperT0 12882 + paperTail256 12882) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12882 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12882 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12882 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12880 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12880 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12882 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12882

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12882
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12882 (61 / 100) 164 (17 / (100 * 12882)) (26 / (10 * 12882)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12882 (61 / 100) 164 (17 / (100 * 12882)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (18265323 / 4000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (141789499 / 100000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (228197249 / 50000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12882 / 12882 * (61 / 100)) ^ 4 * inverseRadius8 (12882 - 1) /
            envelopeGap 12882 (61 / 100) 164 (17 / (100 * 12882)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12882

namespace BstLean.Part266.Row12882
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12882 164 ≤ (2211269783 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12882 164 ≤ (1475434067 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (177310569 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12882 164 ≤ (1756588207 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12882 164 ≤ (1249778961 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12882 164 ≤ (456637497 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (18265323 / 4000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (18265323 / 4000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (141789499 / 100000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (228197249 / 50000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3632727 / 1000000000) : ℝ) ≤ √(17 / (100 * 12882) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12882) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2136897459 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18827473211 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12882) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12882) ≤ (109782143 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12882) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12882 * (164 : ℝ) ^ 2 + 26 / (10 * 12882) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12882) : ℝ)) (tA 12882 * 164 ^ 2 + 26 / (10 * 12882)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3632727 / 1000000000))) * ((18265323 / 4000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3632727 / 1000000000)) ^ 3) * ((141789499 / 100000000000000000000000))) + ((228197249 / 50000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3632727 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12882) : ℝ)) d.D d.V d.P (√(tA 12882) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3632727 / 1000000000)) ^ 2 * (((2136897459 / 1000000000000000)) * ((18827473211 / 500000000000000000)))) + ((228197249 / 50000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12882) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3632727 / 1000000000)) * ((18265323 / 4000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12882) : ℝ)) (tA 12882 * 164 ^ 2 + 26 / (10 * 12882)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((18265323 / 4000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3632727 / 1000000000)) ^ 2) * ((141789499 / 100000000000000000000000)) + ((228197249 / 50000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12882) : ℝ)) (√(26 / (10 * 12882) : ℝ)) d.D d.V d.P (√(tA 12882) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3632727 / 1000000000)) * (((2136897459 / 1000000000000000)) * ((18827473211 / 500000000000000000))) + ((228197249 / 50000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12882) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((18265323 / 4000000000000000000) : ℝ) + ((228197249 / 50000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12882

namespace BstLean.Part266.Row12882
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12882 164 ∧
    0 ≤ (tableEnvelope C).f1 12882 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12882 164 ∧
    0 ≤ (tableEnvelope C).w1 12882 164 ∧ 0 ≤ (tableEnvelope C).w2 12882 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12882 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12882 164 ∧ 0 ≤ d.f1 12882 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12882 164 ∧ 0 ≤ d.w1 12882 164 ∧ 0 ≤ d.w2 12882 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12882 ≤ 2 * (228 / 100 : ℝ) / 12882 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12882 ≤ 2 * (370 / 100 : ℝ) / 12882 := by
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
    (completeRAData (tableEnvelope C) 12882 164).locationBound 12882 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12882 164).energyBound 12882 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12882 164) (d.f1 12882 164) d.f2 ≤
      32 * (((2211269783 / 500000000000000000) : ℝ) + (1475434067 / 1000000000000000000) + (177310569 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12882 164) (d.w1 12882 164)
      (d.w2 12882 164) ≤
      32 * (((1756588207 / 100000000000000000000) : ℝ) + (1249778961 / 100000000000000000000) + (456637497 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12882 164) (d.f1 12882 164) d.f2 ≤
      ((2211269783 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2211269783 / 500000000000000000)) * ((1475434067 / 1000000000000000000)) * (126 / 100) +
      2 * (((1475434067 / 1000000000000000000)) ^ 2 + 2 * ((2211269783 / 500000000000000000)) * ((177310569 / 500000000000000000))) +
      6 * ((1475434067 / 1000000000000000000)) * ((177310569 / 500000000000000000)) * (126 / 100) + 8 * ((177310569 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12882 164) (d.f1 12882 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12882 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12882 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12882 164) (d.f1 12882 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12882 164) (d.w1 12882 164) (d.w2 12882 164)
  have hwexpr0 : 0 ≤ d.w0 12882 164 + d.w1 12882 164 * √(π / 2) +
      2 * d.w2 12882 164 + energyR16 12882 *
      radiusPolynomialRoot16 (d.w0 12882 164) (d.w1 12882 164) (d.w2 12882 164) := by
    positivity
  constructor
  · change (12882 : ℝ) ^ 8 * (mA 12882 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12882 164) (d.f1 12882 164) d.f2 + locationR16 12882 *
        radiusPolynomialRoot16 (d.f0 12882 164) (d.f1 12882 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12882 : ℝ) ^ 8 * (mA 12882 : ℝ) ^ 8 *
        ((((2211269783 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2211269783 / 500000000000000000)) * ((1475434067 / 1000000000000000000)) * (126 / 100) +
          2 * (((1475434067 / 1000000000000000000)) ^ 2 + 2 * ((2211269783 / 500000000000000000)) * ((177310569 / 500000000000000000))) +
          6 * ((1475434067 / 1000000000000000000)) * ((177310569 / 500000000000000000)) * (126 / 100) + 8 * ((177310569 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12882) *
          (32 * (((2211269783 / 500000000000000000) : ℝ) + (1475434067 / 1000000000000000000) + (177310569 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12882 : ℝ) ^ 16 *
      (d.w0 12882 164 + d.w1 12882 164 * √(π / 2) + 2 * d.w2 12882 164 +
        energyR16 12882 * radiusPolynomialRoot16 (d.w0 12882 164) (d.w1 12882 164)
          (d.w2 12882 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12882 : ℝ) ^ 16 *
        (((1756588207 / 100000000000000000000) : ℝ) + ((1249778961 / 100000000000000000000)) * (126 / 100) + 2 * ((456637497 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12882) *
          (32 * (((1756588207 / 100000000000000000000) : ℝ) + (1249778961 / 100000000000000000000) + (456637497 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12882

/-! A coarse bound on the actual paper statistics constant at dimension 12883. -/
namespace BstLean.Part266.Row12883
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12881 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12881 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12881 128 ≤ (13135 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13135 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12883) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12883 : ℕ))
    (by norm_num : (12883 : ℕ) ≤ 16384)
  have ht : paperTail256 12883 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12883 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12883 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12883 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12883 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12883 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12881 128 * √(2 / (12883 : ℝ)) *
      (√(12883 : ℝ) + paperT0 12883 + paperTail256 12883) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12883 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12883 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12883 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12881 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12881 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12883 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12883

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12883
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12883 (61 / 100) 164 (17 / (100 * 12883)) (26 / (10 * 12883)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12883 (61 / 100) 164 (17 / (100 * 12883)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (57065843 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1417454787 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4561084519 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12883 / 12883 * (61 / 100)) ^ 4 * inverseRadius8 (12883 - 1) /
            envelopeGap 12883 (61 / 100) 164 (17 / (100 * 12883)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12883

namespace BstLean.Part266.Row12883
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12883 164 ≤ (221084069 / 50000000000000000)
  f1 : (tableEnvelope C).f1 12883 164 ≤ (1475147759 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (354552323 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12883 164 ≤ (70247167 / 4000000000000000000)
  w1 : (tableEnvelope C).w1 12883 164 ≤ (624743971 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12883 164 ≤ (456531163 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (57065843 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (57065843 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1417454787 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4561084519 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1816293 / 500000000) : ℝ) ≤ √(17 / (100 * 12883) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12883) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2136648647 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37649100747 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12883) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12883) ≤ (54886811 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12883) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12883 * (164 : ℝ) ^ 2 + 26 / (10 * 12883) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12883) : ℝ)) (tA 12883 * 164 ^ 2 + 26 / (10 * 12883)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1816293 / 500000000))) * ((57065843 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1816293 / 500000000)) ^ 3) * ((1417454787 / 1000000000000000000000000))) + ((4561084519 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1816293 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12883) : ℝ)) d.D d.V d.P (√(tA 12883) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1816293 / 500000000)) ^ 2 * (((2136648647 / 1000000000000000)) * ((37649100747 / 1000000000000000000)))) + ((4561084519 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12883) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1816293 / 500000000)) * ((57065843 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12883) : ℝ)) (tA 12883 * 164 ^ 2 + 26 / (10 * 12883)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((57065843 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1816293 / 500000000)) ^ 2) * ((1417454787 / 1000000000000000000000000)) + ((4561084519 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12883) : ℝ)) (√(26 / (10 * 12883) : ℝ)) d.D d.V d.P (√(tA 12883) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1816293 / 500000000)) * (((2136648647 / 1000000000000000)) * ((37649100747 / 1000000000000000000))) + ((4561084519 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12883) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((57065843 / 12500000000000000000) : ℝ) + ((4561084519 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12883

namespace BstLean.Part266.Row12883
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12883 164 ∧
    0 ≤ (tableEnvelope C).f1 12883 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12883 164 ∧
    0 ≤ (tableEnvelope C).w1 12883 164 ∧ 0 ≤ (tableEnvelope C).w2 12883 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12883 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12883 164 ∧ 0 ≤ d.f1 12883 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12883 164 ∧ 0 ≤ d.w1 12883 164 ∧ 0 ≤ d.w2 12883 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12883 ≤ 2 * (228 / 100 : ℝ) / 12883 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12883 ≤ 2 * (370 / 100 : ℝ) / 12883 := by
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
    (completeRAData (tableEnvelope C) 12883 164).locationBound 12883 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12883 164).energyBound 12883 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12883 164) (d.f1 12883 164) d.f2 ≤
      32 * (((221084069 / 50000000000000000) : ℝ) + (1475147759 / 1000000000000000000) + (354552323 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12883 164) (d.w1 12883 164)
      (d.w2 12883 164) ≤
      32 * (((70247167 / 4000000000000000000) : ℝ) + (624743971 / 50000000000000000000) + (456531163 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12883 164) (d.f1 12883 164) d.f2 ≤
      ((221084069 / 50000000000000000) : ℝ) ^ 2 + 2 * ((221084069 / 50000000000000000)) * ((1475147759 / 1000000000000000000)) * (126 / 100) +
      2 * (((1475147759 / 1000000000000000000)) ^ 2 + 2 * ((221084069 / 50000000000000000)) * ((354552323 / 1000000000000000000))) +
      6 * ((1475147759 / 1000000000000000000)) * ((354552323 / 1000000000000000000)) * (126 / 100) + 8 * ((354552323 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12883 164) (d.f1 12883 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12883 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12883 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12883 164) (d.f1 12883 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12883 164) (d.w1 12883 164) (d.w2 12883 164)
  have hwexpr0 : 0 ≤ d.w0 12883 164 + d.w1 12883 164 * √(π / 2) +
      2 * d.w2 12883 164 + energyR16 12883 *
      radiusPolynomialRoot16 (d.w0 12883 164) (d.w1 12883 164) (d.w2 12883 164) := by
    positivity
  constructor
  · change (12883 : ℝ) ^ 8 * (mA 12883 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12883 164) (d.f1 12883 164) d.f2 + locationR16 12883 *
        radiusPolynomialRoot16 (d.f0 12883 164) (d.f1 12883 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12883 : ℝ) ^ 8 * (mA 12883 : ℝ) ^ 8 *
        ((((221084069 / 50000000000000000) : ℝ) ^ 2 + 2 * ((221084069 / 50000000000000000)) * ((1475147759 / 1000000000000000000)) * (126 / 100) +
          2 * (((1475147759 / 1000000000000000000)) ^ 2 + 2 * ((221084069 / 50000000000000000)) * ((354552323 / 1000000000000000000))) +
          6 * ((1475147759 / 1000000000000000000)) * ((354552323 / 1000000000000000000)) * (126 / 100) + 8 * ((354552323 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12883) *
          (32 * (((221084069 / 50000000000000000) : ℝ) + (1475147759 / 1000000000000000000) + (354552323 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12883 : ℝ) ^ 16 *
      (d.w0 12883 164 + d.w1 12883 164 * √(π / 2) + 2 * d.w2 12883 164 +
        energyR16 12883 * radiusPolynomialRoot16 (d.w0 12883 164) (d.w1 12883 164)
          (d.w2 12883 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12883 : ℝ) ^ 16 *
        (((70247167 / 4000000000000000000) : ℝ) + ((624743971 / 50000000000000000000)) * (126 / 100) + 2 * ((456531163 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12883) *
          (32 * (((70247167 / 4000000000000000000) : ℝ) + (624743971 / 50000000000000000000) + (456531163 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12883

/-! A coarse bound on the actual paper statistics constant at dimension 12884. -/
namespace BstLean.Part266.Row12884
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12882 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12882 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12882 128 ≤ (13136 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13136 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12884) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12884 : ℕ))
    (by norm_num : (12884 : ℕ) ≤ 16384)
  have ht : paperTail256 12884 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12884 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12884 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12884 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12884 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12884 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12882 128 * √(2 / (12884 : ℝ)) *
      (√(12884 : ℝ) + paperT0 12884 + paperTail256 12884) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12884 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12884 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12884 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12882 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12882 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12884 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12884

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12884
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12884 (61 / 100) 164 (17 / (100 * 12884)) (26 / (10 * 12884)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12884 (61 / 100) 164 (17 / (100 * 12884)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (228210223 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (708507377 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1139556519 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12884 / 12884 * (61 / 100)) ^ 4 * inverseRadius8 (12884 - 1) /
            envelopeGap 12884 (61 / 100) 164 (17 / (100 * 12884)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12884

namespace BstLean.Part266.Row12884
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12884 164 ≤ (2210411741 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12884 164 ≤ (1474861541 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (44310441 / 125000000000000000)
  w0 : (tableEnvelope C).w0 12884 164 ≤ (877885141 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12884 164 ≤ (624598509 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12884 164 ≤ (228212431 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (228210223 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (228210223 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (708507377 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1139556519 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((726489 / 200000000) : ℝ) ≤ √(17 / (100 * 12884) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12884) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2136399883 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18821628211 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12884) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12884) ≤ (54882551 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12884) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12884 * (164 : ℝ) ^ 2 + 26 / (10 * 12884) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12884) : ℝ)) (tA 12884 * 164 ^ 2 + 26 / (10 * 12884)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((726489 / 200000000))) * ((228210223 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((726489 / 200000000)) ^ 3) * ((708507377 / 500000000000000000000000))) + ((1139556519 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((726489 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12884) : ℝ)) d.D d.V d.P (√(tA 12884) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((726489 / 200000000)) ^ 2 * (((2136399883 / 1000000000000000)) * ((18821628211 / 500000000000000000)))) + ((1139556519 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12884) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((726489 / 200000000)) * ((228210223 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12884) : ℝ)) (tA 12884 * 164 ^ 2 + 26 / (10 * 12884)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((228210223 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((726489 / 200000000)) ^ 2) * ((708507377 / 500000000000000000000000)) + ((1139556519 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12884) : ℝ)) (√(26 / (10 * 12884) : ℝ)) d.D d.V d.P (√(tA 12884) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((726489 / 200000000)) * (((2136399883 / 1000000000000000)) * ((18821628211 / 500000000000000000))) + ((1139556519 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12884) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((228210223 / 50000000000000000000) : ℝ) + ((1139556519 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12884

namespace BstLean.Part266.Row12884
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12884 164 ∧
    0 ≤ (tableEnvelope C).f1 12884 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12884 164 ∧
    0 ≤ (tableEnvelope C).w1 12884 164 ∧ 0 ≤ (tableEnvelope C).w2 12884 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12884 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12884 164 ∧ 0 ≤ d.f1 12884 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12884 164 ∧ 0 ≤ d.w1 12884 164 ∧ 0 ≤ d.w2 12884 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12884 ≤ 2 * (228 / 100 : ℝ) / 12884 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12884 ≤ 2 * (370 / 100 : ℝ) / 12884 := by
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
    (completeRAData (tableEnvelope C) 12884 164).locationBound 12884 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12884 164).energyBound 12884 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12884 164) (d.f1 12884 164) d.f2 ≤
      32 * (((2210411741 / 500000000000000000) : ℝ) + (1474861541 / 1000000000000000000) + (44310441 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12884 164) (d.w1 12884 164)
      (d.w2 12884 164) ≤
      32 * (((877885141 / 50000000000000000000) : ℝ) + (624598509 / 50000000000000000000) + (228212431 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12884 164) (d.f1 12884 164) d.f2 ≤
      ((2210411741 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2210411741 / 500000000000000000)) * ((1474861541 / 1000000000000000000)) * (126 / 100) +
      2 * (((1474861541 / 1000000000000000000)) ^ 2 + 2 * ((2210411741 / 500000000000000000)) * ((44310441 / 125000000000000000))) +
      6 * ((1474861541 / 1000000000000000000)) * ((44310441 / 125000000000000000)) * (126 / 100) + 8 * ((44310441 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12884 164) (d.f1 12884 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12884 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12884 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12884 164) (d.f1 12884 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12884 164) (d.w1 12884 164) (d.w2 12884 164)
  have hwexpr0 : 0 ≤ d.w0 12884 164 + d.w1 12884 164 * √(π / 2) +
      2 * d.w2 12884 164 + energyR16 12884 *
      radiusPolynomialRoot16 (d.w0 12884 164) (d.w1 12884 164) (d.w2 12884 164) := by
    positivity
  constructor
  · change (12884 : ℝ) ^ 8 * (mA 12884 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12884 164) (d.f1 12884 164) d.f2 + locationR16 12884 *
        radiusPolynomialRoot16 (d.f0 12884 164) (d.f1 12884 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12884 : ℝ) ^ 8 * (mA 12884 : ℝ) ^ 8 *
        ((((2210411741 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2210411741 / 500000000000000000)) * ((1474861541 / 1000000000000000000)) * (126 / 100) +
          2 * (((1474861541 / 1000000000000000000)) ^ 2 + 2 * ((2210411741 / 500000000000000000)) * ((44310441 / 125000000000000000))) +
          6 * ((1474861541 / 1000000000000000000)) * ((44310441 / 125000000000000000)) * (126 / 100) + 8 * ((44310441 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12884) *
          (32 * (((2210411741 / 500000000000000000) : ℝ) + (1474861541 / 1000000000000000000) + (44310441 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12884 : ℝ) ^ 16 *
      (d.w0 12884 164 + d.w1 12884 164 * √(π / 2) + 2 * d.w2 12884 164 +
        energyR16 12884 * radiusPolynomialRoot16 (d.w0 12884 164) (d.w1 12884 164)
          (d.w2 12884 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12884 : ℝ) ^ 16 *
        (((877885141 / 50000000000000000000) : ℝ) + ((624598509 / 50000000000000000000)) * (126 / 100) + 2 * ((228212431 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12884) *
          (32 * (((877885141 / 50000000000000000000) : ℝ) + (624598509 / 50000000000000000000) + (228212431 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12884

/-! A coarse bound on the actual paper statistics constant at dimension 12885. -/
namespace BstLean.Part266.Row12885
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12883 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12883 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12883 128 ≤ (13137 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13137 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12885) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12885 : ℕ))
    (by norm_num : (12885 : ℕ) ≤ 16384)
  have ht : paperTail256 12885 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12885 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12885 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12885 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12885 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12885 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12883 128 * √(2 / (12885 : ℝ)) *
      (√(12885 : ℝ) + paperT0 12885 + paperTail256 12885) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12885 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12885 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12885 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12883 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12883 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12885 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12885

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12885
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12885 (61 / 100) 164 (17 / (100 * 12885)) (26 / (10 * 12885)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12885 (61 / 100) 164 (17 / (100 * 12885)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (456314181 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1416574893 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (91107393 / 20000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12885 / 12885 * (61 / 100)) ^ 4 * inverseRadius8 (12885 - 1) /
            envelopeGap 12885 (61 / 100) 164 (17 / (100 * 12885)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12885

namespace BstLean.Part266.Row12885
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12885 164 ≤ (4419965879 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12885 164 ≤ (294915083 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (177207377 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12885 164 ≤ (219420191 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 12885 164 ≤ (1248906191 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12885 164 ≤ (228159297 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (456314181 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (456314181 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1416574893 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (91107393 / 20000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((227019 / 62500000) : ℝ) ≤ √(17 / (100 * 12885) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12885) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (16688681 / 7812500000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18818706737 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12885) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12885) ≤ (109756583 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12885) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12885 * (164 : ℝ) ^ 2 + 26 / (10 * 12885) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12885) : ℝ)) (tA 12885 * 164 ^ 2 + 26 / (10 * 12885)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((227019 / 62500000))) * ((456314181 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((227019 / 62500000)) ^ 3) * ((1416574893 / 1000000000000000000000000))) + ((91107393 / 20000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((227019 / 62500000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12885) : ℝ)) d.D d.V d.P (√(tA 12885) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((227019 / 62500000)) ^ 2 * (((16688681 / 7812500000000)) * ((18818706737 / 500000000000000000)))) + ((91107393 / 20000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12885) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((227019 / 62500000)) * ((456314181 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12885) : ℝ)) (tA 12885 * 164 ^ 2 + 26 / (10 * 12885)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((456314181 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((227019 / 62500000)) ^ 2) * ((1416574893 / 1000000000000000000000000)) + ((91107393 / 20000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12885) : ℝ)) (√(26 / (10 * 12885) : ℝ)) d.D d.V d.P (√(tA 12885) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((227019 / 62500000)) * (((16688681 / 7812500000000)) * ((18818706737 / 500000000000000000))) + ((91107393 / 20000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12885) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((456314181 / 100000000000000000000) : ℝ) + ((91107393 / 20000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12885

namespace BstLean.Part266.Row12885
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12885 164 ∧
    0 ≤ (tableEnvelope C).f1 12885 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12885 164 ∧
    0 ≤ (tableEnvelope C).w1 12885 164 ∧ 0 ≤ (tableEnvelope C).w2 12885 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12885 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12885 164 ∧ 0 ≤ d.f1 12885 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12885 164 ∧ 0 ≤ d.w1 12885 164 ∧ 0 ≤ d.w2 12885 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12885 ≤ 2 * (228 / 100 : ℝ) / 12885 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12885 ≤ 2 * (370 / 100 : ℝ) / 12885 := by
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
    (completeRAData (tableEnvelope C) 12885 164).locationBound 12885 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12885 164).energyBound 12885 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12885 164) (d.f1 12885 164) d.f2 ≤
      32 * (((4419965879 / 1000000000000000000) : ℝ) + (294915083 / 200000000000000000) + (177207377 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12885 164) (d.w1 12885 164)
      (d.w2 12885 164) ≤
      32 * (((219420191 / 12500000000000000000) : ℝ) + (1248906191 / 100000000000000000000) + (228159297 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12885 164) (d.f1 12885 164) d.f2 ≤
      ((4419965879 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4419965879 / 1000000000000000000)) * ((294915083 / 200000000000000000)) * (126 / 100) +
      2 * (((294915083 / 200000000000000000)) ^ 2 + 2 * ((4419965879 / 1000000000000000000)) * ((177207377 / 500000000000000000))) +
      6 * ((294915083 / 200000000000000000)) * ((177207377 / 500000000000000000)) * (126 / 100) + 8 * ((177207377 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12885 164) (d.f1 12885 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12885 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12885 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12885 164) (d.f1 12885 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12885 164) (d.w1 12885 164) (d.w2 12885 164)
  have hwexpr0 : 0 ≤ d.w0 12885 164 + d.w1 12885 164 * √(π / 2) +
      2 * d.w2 12885 164 + energyR16 12885 *
      radiusPolynomialRoot16 (d.w0 12885 164) (d.w1 12885 164) (d.w2 12885 164) := by
    positivity
  constructor
  · change (12885 : ℝ) ^ 8 * (mA 12885 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12885 164) (d.f1 12885 164) d.f2 + locationR16 12885 *
        radiusPolynomialRoot16 (d.f0 12885 164) (d.f1 12885 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12885 : ℝ) ^ 8 * (mA 12885 : ℝ) ^ 8 *
        ((((4419965879 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4419965879 / 1000000000000000000)) * ((294915083 / 200000000000000000)) * (126 / 100) +
          2 * (((294915083 / 200000000000000000)) ^ 2 + 2 * ((4419965879 / 1000000000000000000)) * ((177207377 / 500000000000000000))) +
          6 * ((294915083 / 200000000000000000)) * ((177207377 / 500000000000000000)) * (126 / 100) + 8 * ((177207377 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12885) *
          (32 * (((4419965879 / 1000000000000000000) : ℝ) + (294915083 / 200000000000000000) + (177207377 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12885 : ℝ) ^ 16 *
      (d.w0 12885 164 + d.w1 12885 164 * √(π / 2) + 2 * d.w2 12885 164 +
        energyR16 12885 * radiusPolynomialRoot16 (d.w0 12885 164) (d.w1 12885 164)
          (d.w2 12885 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12885 : ℝ) ^ 16 *
        (((219420191 / 12500000000000000000) : ℝ) + ((1248906191 / 100000000000000000000)) * (126 / 100) + 2 * ((228159297 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12885) *
          (32 * (((219420191 / 12500000000000000000) : ℝ) + (1248906191 / 100000000000000000000) + (228159297 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12885

/-! A coarse bound on the actual paper statistics constant at dimension 12886. -/
namespace BstLean.Part266.Row12886
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12884 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12884 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12884 128 ≤ (13138 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13138 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12886) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12886 : ℕ))
    (by norm_num : (12886 : ℕ) ≤ 16384)
  have ht : paperTail256 12886 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12886 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12886 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12886 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12886 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12886 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12884 128 * √(2 / (12886 : ℝ)) *
      (√(12886 : ℝ) + paperT0 12886 + paperTail256 12886) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12886 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12886 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12886 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12884 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12884 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12886 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12886

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12886
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12886 (61 / 100) 164 (17 / (100 * 12886)) (26 / (10 * 12886)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12886 (61 / 100) 164 (17 / (100 * 12886)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (456207949 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1416135201 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4552515239 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12886 / 12886 * (61 / 100)) ^ 4 * inverseRadius8 (12886 - 1) /
            envelopeGap 12886 (61 / 100) 164 (17 / (100 * 12886)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12886

namespace BstLean.Part266.Row12886
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12886 164 ≤ (4419108561 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12886 164 ≤ (1474289379 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (354345999 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12886 164 ≤ (1754952911 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12886 164 ≤ (1248615459 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12886 164 ≤ (456212359 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (456207949 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (456207949 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1416135201 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4552515239 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3632163 / 1000000000) : ℝ) ≤ √(17 / (100 * 12886) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12886) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2135902501 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7526314373 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12886) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12886) ≤ (21949613 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12886) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12886 * (164 : ℝ) ^ 2 + 26 / (10 * 12886) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12886) : ℝ)) (tA 12886 * 164 ^ 2 + 26 / (10 * 12886)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3632163 / 1000000000))) * ((456207949 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3632163 / 1000000000)) ^ 3) * ((1416135201 / 1000000000000000000000000))) + ((4552515239 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3632163 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12886) : ℝ)) d.D d.V d.P (√(tA 12886) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3632163 / 1000000000)) ^ 2 * (((2135902501 / 1000000000000000)) * ((7526314373 / 200000000000000000)))) + ((4552515239 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12886) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3632163 / 1000000000)) * ((456207949 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12886) : ℝ)) (tA 12886 * 164 ^ 2 + 26 / (10 * 12886)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((456207949 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3632163 / 1000000000)) ^ 2) * ((1416135201 / 1000000000000000000000000)) + ((4552515239 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12886) : ℝ)) (√(26 / (10 * 12886) : ℝ)) d.D d.V d.P (√(tA 12886) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3632163 / 1000000000)) * (((2135902501 / 1000000000000000)) * ((7526314373 / 200000000000000000))) + ((4552515239 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12886) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((456207949 / 100000000000000000000) : ℝ) + ((4552515239 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12886

namespace BstLean.Part266.Row12886
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12886 164 ∧
    0 ≤ (tableEnvelope C).f1 12886 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12886 164 ∧
    0 ≤ (tableEnvelope C).w1 12886 164 ∧ 0 ≤ (tableEnvelope C).w2 12886 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12886 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12886 164 ∧ 0 ≤ d.f1 12886 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12886 164 ∧ 0 ≤ d.w1 12886 164 ∧ 0 ≤ d.w2 12886 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12886 ≤ 2 * (228 / 100 : ℝ) / 12886 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12886 ≤ 2 * (370 / 100 : ℝ) / 12886 := by
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
    (completeRAData (tableEnvelope C) 12886 164).locationBound 12886 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12886 164).energyBound 12886 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12886 164) (d.f1 12886 164) d.f2 ≤
      32 * (((4419108561 / 1000000000000000000) : ℝ) + (1474289379 / 1000000000000000000) + (354345999 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12886 164) (d.w1 12886 164)
      (d.w2 12886 164) ≤
      32 * (((1754952911 / 100000000000000000000) : ℝ) + (1248615459 / 100000000000000000000) + (456212359 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12886 164) (d.f1 12886 164) d.f2 ≤
      ((4419108561 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4419108561 / 1000000000000000000)) * ((1474289379 / 1000000000000000000)) * (126 / 100) +
      2 * (((1474289379 / 1000000000000000000)) ^ 2 + 2 * ((4419108561 / 1000000000000000000)) * ((354345999 / 1000000000000000000))) +
      6 * ((1474289379 / 1000000000000000000)) * ((354345999 / 1000000000000000000)) * (126 / 100) + 8 * ((354345999 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12886 164) (d.f1 12886 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12886 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12886 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12886 164) (d.f1 12886 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12886 164) (d.w1 12886 164) (d.w2 12886 164)
  have hwexpr0 : 0 ≤ d.w0 12886 164 + d.w1 12886 164 * √(π / 2) +
      2 * d.w2 12886 164 + energyR16 12886 *
      radiusPolynomialRoot16 (d.w0 12886 164) (d.w1 12886 164) (d.w2 12886 164) := by
    positivity
  constructor
  · change (12886 : ℝ) ^ 8 * (mA 12886 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12886 164) (d.f1 12886 164) d.f2 + locationR16 12886 *
        radiusPolynomialRoot16 (d.f0 12886 164) (d.f1 12886 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12886 : ℝ) ^ 8 * (mA 12886 : ℝ) ^ 8 *
        ((((4419108561 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4419108561 / 1000000000000000000)) * ((1474289379 / 1000000000000000000)) * (126 / 100) +
          2 * (((1474289379 / 1000000000000000000)) ^ 2 + 2 * ((4419108561 / 1000000000000000000)) * ((354345999 / 1000000000000000000))) +
          6 * ((1474289379 / 1000000000000000000)) * ((354345999 / 1000000000000000000)) * (126 / 100) + 8 * ((354345999 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12886) *
          (32 * (((4419108561 / 1000000000000000000) : ℝ) + (1474289379 / 1000000000000000000) + (354345999 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12886 : ℝ) ^ 16 *
      (d.w0 12886 164 + d.w1 12886 164 * √(π / 2) + 2 * d.w2 12886 164 +
        energyR16 12886 * radiusPolynomialRoot16 (d.w0 12886 164) (d.w1 12886 164)
          (d.w2 12886 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12886 : ℝ) ^ 16 *
        (((1754952911 / 100000000000000000000) : ℝ) + ((1248615459 / 100000000000000000000)) * (126 / 100) + 2 * ((456212359 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12886) *
          (32 * (((1754952911 / 100000000000000000000) : ℝ) + (1248615459 / 100000000000000000000) + (456212359 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12886

/-! A coarse bound on the actual paper statistics constant at dimension 12887. -/
namespace BstLean.Part266.Row12887
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12885 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12885 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12885 128 ≤ (13139 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13139 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12887) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12887 : ℕ))
    (by norm_num : (12887 : ℕ) ≤ 16384)
  have ht : paperTail256 12887 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12887 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12887 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12887 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12887 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12887 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12885 128 * √(2 / (12887 : ℝ)) *
      (√(12887 : ℝ) + paperT0 12887 + paperTail256 12887) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12887 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12887 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12887 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12885 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12885 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12887 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12887

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12887
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12887 (61 / 100) 164 (17 / (100 * 12887)) (26 / (10 * 12887)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12887 (61 / 100) 164 (17 / (100 * 12887)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (1824407 / 400000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1415695681 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4549662843 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12887 / 12887 * (61 / 100)) ^ 4 * inverseRadius8 (12887 - 1) /
            envelopeGap 12887 (61 / 100) 164 (17 / (100 * 12887)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12887

namespace BstLean.Part266.Row12887
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12887 164 ≤ (2209125769 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12887 164 ≤ (294800687 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (70855453 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12887 164 ≤ (350908887 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12887 164 ≤ (1248324823 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12887 164 ≤ (228053079 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (1824407 / 400000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (1824407 / 400000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1415695681 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4549662843 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1816011 / 500000000) : ℝ) ≤ √(17 / (100 * 12887) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12887) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1067826941 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7525146327 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12887) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12887) ≤ (109739549 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12887) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12887 * (164 : ℝ) ^ 2 + 26 / (10 * 12887) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12887) : ℝ)) (tA 12887 * 164 ^ 2 + 26 / (10 * 12887)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1816011 / 500000000))) * ((1824407 / 400000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1816011 / 500000000)) ^ 3) * ((1415695681 / 1000000000000000000000000))) + ((4549662843 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1816011 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12887) : ℝ)) d.D d.V d.P (√(tA 12887) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1816011 / 500000000)) ^ 2 * (((1067826941 / 500000000000000)) * ((7525146327 / 200000000000000000)))) + ((4549662843 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12887) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1816011 / 500000000)) * ((1824407 / 400000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12887) : ℝ)) (tA 12887 * 164 ^ 2 + 26 / (10 * 12887)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((1824407 / 400000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1816011 / 500000000)) ^ 2) * ((1415695681 / 1000000000000000000000000)) + ((4549662843 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12887) : ℝ)) (√(26 / (10 * 12887) : ℝ)) d.D d.V d.P (√(tA 12887) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1816011 / 500000000)) * (((1067826941 / 500000000000000)) * ((7525146327 / 200000000000000000))) + ((4549662843 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12887) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((1824407 / 400000000000000000) : ℝ) + ((4549662843 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12887

namespace BstLean.Part266.Row12887
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12887 164 ∧
    0 ≤ (tableEnvelope C).f1 12887 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12887 164 ∧
    0 ≤ (tableEnvelope C).w1 12887 164 ∧ 0 ≤ (tableEnvelope C).w2 12887 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12887 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12887 164 ∧ 0 ≤ d.f1 12887 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12887 164 ∧ 0 ≤ d.w1 12887 164 ∧ 0 ≤ d.w2 12887 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12887 ≤ 2 * (228 / 100 : ℝ) / 12887 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12887 ≤ 2 * (370 / 100 : ℝ) / 12887 := by
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
    (completeRAData (tableEnvelope C) 12887 164).locationBound 12887 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12887 164).energyBound 12887 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12887 164) (d.f1 12887 164) d.f2 ≤
      32 * (((2209125769 / 500000000000000000) : ℝ) + (294800687 / 200000000000000000) + (70855453 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12887 164) (d.w1 12887 164)
      (d.w2 12887 164) ≤
      32 * (((350908887 / 20000000000000000000) : ℝ) + (1248324823 / 100000000000000000000) + (228053079 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12887 164) (d.f1 12887 164) d.f2 ≤
      ((2209125769 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2209125769 / 500000000000000000)) * ((294800687 / 200000000000000000)) * (126 / 100) +
      2 * (((294800687 / 200000000000000000)) ^ 2 + 2 * ((2209125769 / 500000000000000000)) * ((70855453 / 200000000000000000))) +
      6 * ((294800687 / 200000000000000000)) * ((70855453 / 200000000000000000)) * (126 / 100) + 8 * ((70855453 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12887 164) (d.f1 12887 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12887 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12887 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12887 164) (d.f1 12887 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12887 164) (d.w1 12887 164) (d.w2 12887 164)
  have hwexpr0 : 0 ≤ d.w0 12887 164 + d.w1 12887 164 * √(π / 2) +
      2 * d.w2 12887 164 + energyR16 12887 *
      radiusPolynomialRoot16 (d.w0 12887 164) (d.w1 12887 164) (d.w2 12887 164) := by
    positivity
  constructor
  · change (12887 : ℝ) ^ 8 * (mA 12887 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12887 164) (d.f1 12887 164) d.f2 + locationR16 12887 *
        radiusPolynomialRoot16 (d.f0 12887 164) (d.f1 12887 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12887 : ℝ) ^ 8 * (mA 12887 : ℝ) ^ 8 *
        ((((2209125769 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2209125769 / 500000000000000000)) * ((294800687 / 200000000000000000)) * (126 / 100) +
          2 * (((294800687 / 200000000000000000)) ^ 2 + 2 * ((2209125769 / 500000000000000000)) * ((70855453 / 200000000000000000))) +
          6 * ((294800687 / 200000000000000000)) * ((70855453 / 200000000000000000)) * (126 / 100) + 8 * ((70855453 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12887) *
          (32 * (((2209125769 / 500000000000000000) : ℝ) + (294800687 / 200000000000000000) + (70855453 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12887 : ℝ) ^ 16 *
      (d.w0 12887 164 + d.w1 12887 164 * √(π / 2) + 2 * d.w2 12887 164 +
        energyR16 12887 * radiusPolynomialRoot16 (d.w0 12887 164) (d.w1 12887 164)
          (d.w2 12887 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12887 : ℝ) ^ 16 *
        (((350908887 / 20000000000000000000) : ℝ) + ((1248324823 / 100000000000000000000)) * (126 / 100) + 2 * ((228053079 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12887) *
          (32 * (((350908887 / 20000000000000000000) : ℝ) + (1248324823 / 100000000000000000000) + (228053079 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12887

/-! A coarse bound on the actual paper statistics constant at dimension 12888. -/
namespace BstLean.Part266.Row12888
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12886 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12886 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12886 128 ≤ (13140 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13140 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12888) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12888 : ℕ))
    (by norm_num : (12888 : ℕ) ≤ 16384)
  have ht : paperTail256 12888 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12888 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12888 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12888 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12888 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12888 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12886 128 * √(2 / (12888 : ℝ)) *
      (√(12888 : ℝ) + paperT0 12888 + paperTail256 12888) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12888 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12888 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12888 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12886 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12886 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12888 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12888

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12888
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12888 (61 / 100) 164 (17 / (100 * 12888)) (26 / (10 * 12888)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12888 (61 / 100) 164 (17 / (100 * 12888)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (455995583 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1415256331 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (227340623 / 50000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12888 / 12888 * (61 / 100)) ^ 4 * inverseRadius8 (12888 - 1) /
            envelopeGap 12888 (61 / 100) 164 (17 / (100 * 12888)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12888

namespace BstLean.Part266.Row12888
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12888 164 ≤ (4417394803 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12888 164 ≤ (73685879 / 50000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (354208551 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12888 164 ≤ (350827219 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12888 164 ≤ (624017141 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12888 164 ≤ (113999997 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (455995583 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (455995583 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1415256331 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (227340623 / 50000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3631881 / 1000000000) : ℝ) ≤ √(17 / (100 * 12888) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12888) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2135405309 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37619892757 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12888) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12888) ≤ (54865517 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12888) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12888 * (164 : ℝ) ^ 2 + 26 / (10 * 12888) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12888) : ℝ)) (tA 12888 * 164 ^ 2 + 26 / (10 * 12888)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3631881 / 1000000000))) * ((455995583 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3631881 / 1000000000)) ^ 3) * ((1415256331 / 1000000000000000000000000))) + ((227340623 / 50000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3631881 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12888) : ℝ)) d.D d.V d.P (√(tA 12888) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3631881 / 1000000000)) ^ 2 * (((2135405309 / 1000000000000000)) * ((37619892757 / 1000000000000000000)))) + ((227340623 / 50000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12888) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3631881 / 1000000000)) * ((455995583 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12888) : ℝ)) (tA 12888 * 164 ^ 2 + 26 / (10 * 12888)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((455995583 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3631881 / 1000000000)) ^ 2) * ((1415256331 / 1000000000000000000000000)) + ((227340623 / 50000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12888) : ℝ)) (√(26 / (10 * 12888) : ℝ)) d.D d.V d.P (√(tA 12888) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3631881 / 1000000000)) * (((2135405309 / 1000000000000000)) * ((37619892757 / 1000000000000000000))) + ((227340623 / 50000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12888) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((455995583 / 100000000000000000000) : ℝ) + ((227340623 / 50000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12888

namespace BstLean.Part266.Row12888
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12888 164 ∧
    0 ≤ (tableEnvelope C).f1 12888 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12888 164 ∧
    0 ≤ (tableEnvelope C).w1 12888 164 ∧ 0 ≤ (tableEnvelope C).w2 12888 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12888 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12888 164 ∧ 0 ≤ d.f1 12888 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12888 164 ∧ 0 ≤ d.w1 12888 164 ∧ 0 ≤ d.w2 12888 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12888 ≤ 2 * (228 / 100 : ℝ) / 12888 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12888 ≤ 2 * (370 / 100 : ℝ) / 12888 := by
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
    (completeRAData (tableEnvelope C) 12888 164).locationBound 12888 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12888 164).energyBound 12888 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12888 164) (d.f1 12888 164) d.f2 ≤
      32 * (((4417394803 / 1000000000000000000) : ℝ) + (73685879 / 50000000000000000) + (354208551 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12888 164) (d.w1 12888 164)
      (d.w2 12888 164) ≤
      32 * (((350827219 / 20000000000000000000) : ℝ) + (624017141 / 50000000000000000000) + (113999997 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12888 164) (d.f1 12888 164) d.f2 ≤
      ((4417394803 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4417394803 / 1000000000000000000)) * ((73685879 / 50000000000000000)) * (126 / 100) +
      2 * (((73685879 / 50000000000000000)) ^ 2 + 2 * ((4417394803 / 1000000000000000000)) * ((354208551 / 1000000000000000000))) +
      6 * ((73685879 / 50000000000000000)) * ((354208551 / 1000000000000000000)) * (126 / 100) + 8 * ((354208551 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12888 164) (d.f1 12888 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12888 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12888 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12888 164) (d.f1 12888 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12888 164) (d.w1 12888 164) (d.w2 12888 164)
  have hwexpr0 : 0 ≤ d.w0 12888 164 + d.w1 12888 164 * √(π / 2) +
      2 * d.w2 12888 164 + energyR16 12888 *
      radiusPolynomialRoot16 (d.w0 12888 164) (d.w1 12888 164) (d.w2 12888 164) := by
    positivity
  constructor
  · change (12888 : ℝ) ^ 8 * (mA 12888 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12888 164) (d.f1 12888 164) d.f2 + locationR16 12888 *
        radiusPolynomialRoot16 (d.f0 12888 164) (d.f1 12888 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12888 : ℝ) ^ 8 * (mA 12888 : ℝ) ^ 8 *
        ((((4417394803 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4417394803 / 1000000000000000000)) * ((73685879 / 50000000000000000)) * (126 / 100) +
          2 * (((73685879 / 50000000000000000)) ^ 2 + 2 * ((4417394803 / 1000000000000000000)) * ((354208551 / 1000000000000000000))) +
          6 * ((73685879 / 50000000000000000)) * ((354208551 / 1000000000000000000)) * (126 / 100) + 8 * ((354208551 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12888) *
          (32 * (((4417394803 / 1000000000000000000) : ℝ) + (73685879 / 50000000000000000) + (354208551 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12888 : ℝ) ^ 16 *
      (d.w0 12888 164 + d.w1 12888 164 * √(π / 2) + 2 * d.w2 12888 164 +
        energyR16 12888 * radiusPolynomialRoot16 (d.w0 12888 164) (d.w1 12888 164)
          (d.w2 12888 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12888 : ℝ) ^ 16 *
        (((350827219 / 20000000000000000000) : ℝ) + ((624017141 / 50000000000000000000)) * (126 / 100) + 2 * ((113999997 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12888) *
          (32 * (((350827219 / 20000000000000000000) : ℝ) + (624017141 / 50000000000000000000) + (113999997 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12888

/-! A coarse bound on the actual paper statistics constant at dimension 12889. -/
namespace BstLean.Part266.Row12889
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12887 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12887 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12887 128 ≤ (13141 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13141 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12889) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12889 : ℕ))
    (by norm_num : (12889 : ℕ) ≤ 16384)
  have ht : paperTail256 12889 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12889 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12889 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12889 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12889 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12889 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12887 128 * √(2 / (12889 : ℝ)) *
      (√(12889 : ℝ) + paperT0 12889 + paperTail256 12889) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12889 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12889 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12889 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12887 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12887 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12889 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12889

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12889
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12889 (61 / 100) 164 (17 / (100 * 12889)) (26 / (10 * 12889)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12889 (61 / 100) 164 (17 / (100 * 12889)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (9117789 / 2000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1414817151 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4543964087 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12889 / 12889 * (61 / 100)) ^ 4 * inverseRadius8 (12889 - 1) /
            envelopeGap 12889 (61 / 100) 164 (17 / (100 * 12889)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12889

namespace BstLean.Part266.Row12889
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12889 164 ≤ (4416538357 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12889 164 ≤ (1473431817 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (177069929 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12889 164 ≤ (876863947 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12889 164 ≤ (1247743837 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12889 164 ≤ (113973463 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (9117789 / 2000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (9117789 / 2000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1414817151 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4543964087 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((181587 / 50000000) : ℝ) ≤ √(17 / (100 * 12889) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12889) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1067578393 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37614055233 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12889) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12889) ≤ (109722521 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12889) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12889 * (164 : ℝ) ^ 2 + 26 / (10 * 12889) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12889) : ℝ)) (tA 12889 * 164 ^ 2 + 26 / (10 * 12889)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((181587 / 50000000))) * ((9117789 / 2000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((181587 / 50000000)) ^ 3) * ((1414817151 / 1000000000000000000000000))) + ((4543964087 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((181587 / 50000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12889) : ℝ)) d.D d.V d.P (√(tA 12889) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((181587 / 50000000)) ^ 2 * (((1067578393 / 500000000000000)) * ((37614055233 / 1000000000000000000)))) + ((4543964087 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12889) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((181587 / 50000000)) * ((9117789 / 2000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12889) : ℝ)) (tA 12889 * 164 ^ 2 + 26 / (10 * 12889)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((9117789 / 2000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((181587 / 50000000)) ^ 2) * ((1414817151 / 1000000000000000000000000)) + ((4543964087 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12889) : ℝ)) (√(26 / (10 * 12889) : ℝ)) d.D d.V d.P (√(tA 12889) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((181587 / 50000000)) * (((1067578393 / 500000000000000)) * ((37614055233 / 1000000000000000000))) + ((4543964087 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12889) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((9117789 / 2000000000000000000) : ℝ) + ((4543964087 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12889

namespace BstLean.Part266.Row12889
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12889 164 ∧
    0 ≤ (tableEnvelope C).f1 12889 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12889 164 ∧
    0 ≤ (tableEnvelope C).w1 12889 164 ∧ 0 ≤ (tableEnvelope C).w2 12889 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12889 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12889 164 ∧ 0 ≤ d.f1 12889 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12889 164 ∧ 0 ≤ d.w1 12889 164 ∧ 0 ≤ d.w2 12889 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12889 ≤ 2 * (228 / 100 : ℝ) / 12889 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12889 ≤ 2 * (370 / 100 : ℝ) / 12889 := by
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
    (completeRAData (tableEnvelope C) 12889 164).locationBound 12889 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12889 164).energyBound 12889 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12889 164) (d.f1 12889 164) d.f2 ≤
      32 * (((4416538357 / 1000000000000000000) : ℝ) + (1473431817 / 1000000000000000000) + (177069929 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12889 164) (d.w1 12889 164)
      (d.w2 12889 164) ≤
      32 * (((876863947 / 50000000000000000000) : ℝ) + (1247743837 / 100000000000000000000) + (113973463 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12889 164) (d.f1 12889 164) d.f2 ≤
      ((4416538357 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4416538357 / 1000000000000000000)) * ((1473431817 / 1000000000000000000)) * (126 / 100) +
      2 * (((1473431817 / 1000000000000000000)) ^ 2 + 2 * ((4416538357 / 1000000000000000000)) * ((177069929 / 500000000000000000))) +
      6 * ((1473431817 / 1000000000000000000)) * ((177069929 / 500000000000000000)) * (126 / 100) + 8 * ((177069929 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12889 164) (d.f1 12889 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12889 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12889 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12889 164) (d.f1 12889 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12889 164) (d.w1 12889 164) (d.w2 12889 164)
  have hwexpr0 : 0 ≤ d.w0 12889 164 + d.w1 12889 164 * √(π / 2) +
      2 * d.w2 12889 164 + energyR16 12889 *
      radiusPolynomialRoot16 (d.w0 12889 164) (d.w1 12889 164) (d.w2 12889 164) := by
    positivity
  constructor
  · change (12889 : ℝ) ^ 8 * (mA 12889 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12889 164) (d.f1 12889 164) d.f2 + locationR16 12889 *
        radiusPolynomialRoot16 (d.f0 12889 164) (d.f1 12889 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12889 : ℝ) ^ 8 * (mA 12889 : ℝ) ^ 8 *
        ((((4416538357 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4416538357 / 1000000000000000000)) * ((1473431817 / 1000000000000000000)) * (126 / 100) +
          2 * (((1473431817 / 1000000000000000000)) ^ 2 + 2 * ((4416538357 / 1000000000000000000)) * ((177069929 / 500000000000000000))) +
          6 * ((1473431817 / 1000000000000000000)) * ((177069929 / 500000000000000000)) * (126 / 100) + 8 * ((177069929 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12889) *
          (32 * (((4416538357 / 1000000000000000000) : ℝ) + (1473431817 / 1000000000000000000) + (177069929 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12889 : ℝ) ^ 16 *
      (d.w0 12889 164 + d.w1 12889 164 * √(π / 2) + 2 * d.w2 12889 164 +
        energyR16 12889 * radiusPolynomialRoot16 (d.w0 12889 164) (d.w1 12889 164)
          (d.w2 12889 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12889 : ℝ) ^ 16 *
        (((876863947 / 50000000000000000000) : ℝ) + ((1247743837 / 100000000000000000000)) * (126 / 100) + 2 * ((113973463 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12889) *
          (32 * (((876863947 / 50000000000000000000) : ℝ) + (1247743837 / 100000000000000000000) + (113973463 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12889

/-! A coarse bound on the actual paper statistics constant at dimension 12890. -/
namespace BstLean.Part266.Row12890
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12888 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12888 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12888 128 ≤ (13142 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13142 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12890) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12890 : ℕ))
    (by norm_num : (12890 : ℕ) ≤ 16384)
  have ht : paperTail256 12890 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12890 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12890 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12890 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12890 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12890 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12888 128 * √(2 / (12890 : ℝ)) *
      (√(12890 : ℝ) + paperT0 12890 + paperTail256 12890) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12890 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12890 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12890 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12888 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12888 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12890 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12890

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12890
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12890 (61 / 100) 164 (17 / (100 * 12890)) (26 / (10 * 12890)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12890 (61 / 100) 164 (17 / (100 * 12890)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (9115667 / 2000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (707189071 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4541117723 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12890 / 12890 * (61 / 100)) ^ 4 * inverseRadius8 (12890 - 1) /
            envelopeGap 12890 (61 / 100) 164 (17 / (100 * 12890)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12890

namespace BstLean.Part266.Row12890
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12890 164 ≤ (1103920551 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12890 164 ≤ (736573073 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (70814237 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12890 164 ≤ (1753319833 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12890 164 ≤ (1247453489 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12890 164 ≤ (455787749 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (9115667 / 2000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (9115667 / 2000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (707189071 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4541117723 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3631599 / 1000000000) : ℝ) ≤ √(17 / (100 * 12890) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12890) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (266863539 / 125000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9402054769 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12890) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12890) ≤ (13714251 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12890) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12890 * (164 : ℝ) ^ 2 + 26 / (10 * 12890) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12890) : ℝ)) (tA 12890 * 164 ^ 2 + 26 / (10 * 12890)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3631599 / 1000000000))) * ((9115667 / 2000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3631599 / 1000000000)) ^ 3) * ((707189071 / 500000000000000000000000))) + ((4541117723 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3631599 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12890) : ℝ)) d.D d.V d.P (√(tA 12890) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3631599 / 1000000000)) ^ 2 * (((266863539 / 125000000000000)) * ((9402054769 / 250000000000000000)))) + ((4541117723 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12890) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3631599 / 1000000000)) * ((9115667 / 2000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12890) : ℝ)) (tA 12890 * 164 ^ 2 + 26 / (10 * 12890)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((9115667 / 2000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3631599 / 1000000000)) ^ 2) * ((707189071 / 500000000000000000000000)) + ((4541117723 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12890) : ℝ)) (√(26 / (10 * 12890) : ℝ)) d.D d.V d.P (√(tA 12890) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3631599 / 1000000000)) * (((266863539 / 125000000000000)) * ((9402054769 / 250000000000000000))) + ((4541117723 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12890) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((9115667 / 2000000000000000000) : ℝ) + ((4541117723 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12890

namespace BstLean.Part266.Row12890
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12890 164 ∧
    0 ≤ (tableEnvelope C).f1 12890 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12890 164 ∧
    0 ≤ (tableEnvelope C).w1 12890 164 ∧ 0 ≤ (tableEnvelope C).w2 12890 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12890 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12890 164 ∧ 0 ≤ d.f1 12890 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12890 164 ∧ 0 ≤ d.w1 12890 164 ∧ 0 ≤ d.w2 12890 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12890 ≤ 2 * (228 / 100 : ℝ) / 12890 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12890 ≤ 2 * (370 / 100 : ℝ) / 12890 := by
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
    (completeRAData (tableEnvelope C) 12890 164).locationBound 12890 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12890 164).energyBound 12890 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12890 164) (d.f1 12890 164) d.f2 ≤
      32 * (((1103920551 / 250000000000000000) : ℝ) + (736573073 / 500000000000000000) + (70814237 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12890 164) (d.w1 12890 164)
      (d.w2 12890 164) ≤
      32 * (((1753319833 / 100000000000000000000) : ℝ) + (1247453489 / 100000000000000000000) + (455787749 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12890 164) (d.f1 12890 164) d.f2 ≤
      ((1103920551 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1103920551 / 250000000000000000)) * ((736573073 / 500000000000000000)) * (126 / 100) +
      2 * (((736573073 / 500000000000000000)) ^ 2 + 2 * ((1103920551 / 250000000000000000)) * ((70814237 / 200000000000000000))) +
      6 * ((736573073 / 500000000000000000)) * ((70814237 / 200000000000000000)) * (126 / 100) + 8 * ((70814237 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12890 164) (d.f1 12890 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12890 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12890 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12890 164) (d.f1 12890 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12890 164) (d.w1 12890 164) (d.w2 12890 164)
  have hwexpr0 : 0 ≤ d.w0 12890 164 + d.w1 12890 164 * √(π / 2) +
      2 * d.w2 12890 164 + energyR16 12890 *
      radiusPolynomialRoot16 (d.w0 12890 164) (d.w1 12890 164) (d.w2 12890 164) := by
    positivity
  constructor
  · change (12890 : ℝ) ^ 8 * (mA 12890 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12890 164) (d.f1 12890 164) d.f2 + locationR16 12890 *
        radiusPolynomialRoot16 (d.f0 12890 164) (d.f1 12890 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12890 : ℝ) ^ 8 * (mA 12890 : ℝ) ^ 8 *
        ((((1103920551 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1103920551 / 250000000000000000)) * ((736573073 / 500000000000000000)) * (126 / 100) +
          2 * (((736573073 / 500000000000000000)) ^ 2 + 2 * ((1103920551 / 250000000000000000)) * ((70814237 / 200000000000000000))) +
          6 * ((736573073 / 500000000000000000)) * ((70814237 / 200000000000000000)) * (126 / 100) + 8 * ((70814237 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12890) *
          (32 * (((1103920551 / 250000000000000000) : ℝ) + (736573073 / 500000000000000000) + (70814237 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12890 : ℝ) ^ 16 *
      (d.w0 12890 164 + d.w1 12890 164 * √(π / 2) + 2 * d.w2 12890 164 +
        energyR16 12890 * radiusPolynomialRoot16 (d.w0 12890 164) (d.w1 12890 164)
          (d.w2 12890 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12890 : ℝ) ^ 16 *
        (((1753319833 / 100000000000000000000) : ℝ) + ((1247453489 / 100000000000000000000)) * (126 / 100) + 2 * ((455787749 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12890) *
          (32 * (((1753319833 / 100000000000000000000) : ℝ) + (1247453489 / 100000000000000000000) + (455787749 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12890

/-! A coarse bound on the actual paper statistics constant at dimension 12891. -/
namespace BstLean.Part266.Row12891
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12889 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12889 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12889 128 ≤ (13143 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13143 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12891) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12891 : ℕ))
    (by norm_num : (12891 : ℕ) ≤ 16384)
  have ht : paperTail256 12891 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12891 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12891 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12891 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12891 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12891 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12889 128 * √(2 / (12891 : ℝ)) *
      (√(12891 : ℝ) + paperT0 12891 + paperTail256 12891) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12891 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12891 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12891 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12889 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12889 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12891 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12891

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12891
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12891 (61 / 100) 164 (17 / (100 * 12891)) (26 / (10 * 12891)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12891 (61 / 100) 164 (17 / (100 * 12891)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (227838641 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1413939303 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4538273367 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12891 / 12891 * (61 / 100)) ^ 4 * inverseRadius8 (12891 - 1) /
            envelopeGap 12891 (61 / 100) 164 (17 / (100 * 12891)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12891

namespace BstLean.Part266.Row12891
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12891 164 ≤ (441482283 / 100000000000000000)
  f1 : (tableEnvelope C).f1 12891 164 ≤ (1472859753 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (177001217 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12891 164 ≤ (876455597 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12891 164 ≤ (311790723 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12891 164 ≤ (455681679 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (227838641 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (227838641 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1413939303 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4538273367 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3631459 / 1000000000) : ℝ) ≤ √(17 / (100 * 12891) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12891) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (533664971 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37602384273 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12891) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12891) ≤ (54852749 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12891) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12891 * (164 : ℝ) ^ 2 + 26 / (10 * 12891) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12891) : ℝ)) (tA 12891 * 164 ^ 2 + 26 / (10 * 12891)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3631459 / 1000000000))) * ((227838641 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3631459 / 1000000000)) ^ 3) * ((1413939303 / 1000000000000000000000000))) + ((4538273367 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3631459 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12891) : ℝ)) d.D d.V d.P (√(tA 12891) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3631459 / 1000000000)) ^ 2 * (((533664971 / 250000000000000)) * ((37602384273 / 1000000000000000000)))) + ((4538273367 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12891) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3631459 / 1000000000)) * ((227838641 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12891) : ℝ)) (tA 12891 * 164 ^ 2 + 26 / (10 * 12891)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((227838641 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3631459 / 1000000000)) ^ 2) * ((1413939303 / 1000000000000000000000000)) + ((4538273367 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12891) : ℝ)) (√(26 / (10 * 12891) : ℝ)) d.D d.V d.P (√(tA 12891) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3631459 / 1000000000)) * (((533664971 / 250000000000000)) * ((37602384273 / 1000000000000000000))) + ((4538273367 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12891) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((227838641 / 50000000000000000000) : ℝ) + ((4538273367 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12891

namespace BstLean.Part266.Row12891
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12891 164 ∧
    0 ≤ (tableEnvelope C).f1 12891 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12891 164 ∧
    0 ≤ (tableEnvelope C).w1 12891 164 ∧ 0 ≤ (tableEnvelope C).w2 12891 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12891 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12891 164 ∧ 0 ≤ d.f1 12891 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12891 164 ∧ 0 ≤ d.w1 12891 164 ∧ 0 ≤ d.w2 12891 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12891 ≤ 2 * (228 / 100 : ℝ) / 12891 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12891 ≤ 2 * (370 / 100 : ℝ) / 12891 := by
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
    (completeRAData (tableEnvelope C) 12891 164).locationBound 12891 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12891 164).energyBound 12891 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12891 164) (d.f1 12891 164) d.f2 ≤
      32 * (((441482283 / 100000000000000000) : ℝ) + (1472859753 / 1000000000000000000) + (177001217 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12891 164) (d.w1 12891 164)
      (d.w2 12891 164) ≤
      32 * (((876455597 / 50000000000000000000) : ℝ) + (311790723 / 25000000000000000000) + (455681679 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12891 164) (d.f1 12891 164) d.f2 ≤
      ((441482283 / 100000000000000000) : ℝ) ^ 2 + 2 * ((441482283 / 100000000000000000)) * ((1472859753 / 1000000000000000000)) * (126 / 100) +
      2 * (((1472859753 / 1000000000000000000)) ^ 2 + 2 * ((441482283 / 100000000000000000)) * ((177001217 / 500000000000000000))) +
      6 * ((1472859753 / 1000000000000000000)) * ((177001217 / 500000000000000000)) * (126 / 100) + 8 * ((177001217 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12891 164) (d.f1 12891 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12891 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12891 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12891 164) (d.f1 12891 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12891 164) (d.w1 12891 164) (d.w2 12891 164)
  have hwexpr0 : 0 ≤ d.w0 12891 164 + d.w1 12891 164 * √(π / 2) +
      2 * d.w2 12891 164 + energyR16 12891 *
      radiusPolynomialRoot16 (d.w0 12891 164) (d.w1 12891 164) (d.w2 12891 164) := by
    positivity
  constructor
  · change (12891 : ℝ) ^ 8 * (mA 12891 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12891 164) (d.f1 12891 164) d.f2 + locationR16 12891 *
        radiusPolynomialRoot16 (d.f0 12891 164) (d.f1 12891 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12891 : ℝ) ^ 8 * (mA 12891 : ℝ) ^ 8 *
        ((((441482283 / 100000000000000000) : ℝ) ^ 2 + 2 * ((441482283 / 100000000000000000)) * ((1472859753 / 1000000000000000000)) * (126 / 100) +
          2 * (((1472859753 / 1000000000000000000)) ^ 2 + 2 * ((441482283 / 100000000000000000)) * ((177001217 / 500000000000000000))) +
          6 * ((1472859753 / 1000000000000000000)) * ((177001217 / 500000000000000000)) * (126 / 100) + 8 * ((177001217 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12891) *
          (32 * (((441482283 / 100000000000000000) : ℝ) + (1472859753 / 1000000000000000000) + (177001217 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12891 : ℝ) ^ 16 *
      (d.w0 12891 164 + d.w1 12891 164 * √(π / 2) + 2 * d.w2 12891 164 +
        energyR16 12891 * radiusPolynomialRoot16 (d.w0 12891 164) (d.w1 12891 164)
          (d.w2 12891 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12891 : ℝ) ^ 16 *
        (((876455597 / 50000000000000000000) : ℝ) + ((311790723 / 25000000000000000000)) * (126 / 100) + 2 * ((455681679 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12891) *
          (32 * (((876455597 / 50000000000000000000) : ℝ) + (311790723 / 25000000000000000000) + (455681679 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12891

/-! A coarse bound on the actual paper statistics constant at dimension 12892. -/
namespace BstLean.Part266.Row12892
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12890 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12890 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12890 128 ≤ (13144 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13144 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12892) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12892 : ℕ))
    (by norm_num : (12892 : ℕ) ≤ 16384)
  have ht : paperTail256 12892 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12892 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12892 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12892 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12892 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12892 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12890 128 * √(2 / (12892 : ℝ)) *
      (√(12892 : ℝ) + paperT0 12892 + paperTail256 12892) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12892 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12892 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12892 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12890 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12890 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12892 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12892

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12892
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12892 (61 / 100) 164 (17 / (100 * 12892)) (26 / (10 * 12892)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12892 (61 / 100) 164 (17 / (100 * 12892)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (28473203 / 6250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (706750317 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2267715509 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12892 / 12892 * (61 / 100)) ^ 4 * inverseRadius8 (12892 - 1) /
            envelopeGap 12892 (61 / 100) 164 (17 / (100 * 12892)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12892

namespace BstLean.Part266.Row12892
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12892 164 ≤ (551745907 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12892 164 ≤ (1472574263 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (353933801 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12892 164 ≤ (1752503409 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12892 164 ≤ (38964773 / 3125000000000000000)
  w2 : (tableEnvelope C).w2 12892 164 ≤ (227787821 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (28473203 / 6250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (28473203 / 6250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (706750317 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2267715509 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1815659 / 500000000) : ℝ) ≤ √(17 / (100 * 12892) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12892) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2134411507 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18798275413 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12892) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12892) ≤ (27424247 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12892) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12892 * (164 : ℝ) ^ 2 + 26 / (10 * 12892) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12892) : ℝ)) (tA 12892 * 164 ^ 2 + 26 / (10 * 12892)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1815659 / 500000000))) * ((28473203 / 6250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1815659 / 500000000)) ^ 3) * ((706750317 / 500000000000000000000000))) + ((2267715509 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1815659 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12892) : ℝ)) d.D d.V d.P (√(tA 12892) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1815659 / 500000000)) ^ 2 * (((2134411507 / 1000000000000000)) * ((18798275413 / 500000000000000000)))) + ((2267715509 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12892) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1815659 / 500000000)) * ((28473203 / 6250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12892) : ℝ)) (tA 12892 * 164 ^ 2 + 26 / (10 * 12892)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((28473203 / 6250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1815659 / 500000000)) ^ 2) * ((706750317 / 500000000000000000000000)) + ((2267715509 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12892) : ℝ)) (√(26 / (10 * 12892) : ℝ)) d.D d.V d.P (√(tA 12892) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1815659 / 500000000)) * (((2134411507 / 1000000000000000)) * ((18798275413 / 500000000000000000))) + ((2267715509 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12892) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((28473203 / 6250000000000000000) : ℝ) + ((2267715509 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12892

namespace BstLean.Part266.Row12892
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12892 164 ∧
    0 ≤ (tableEnvelope C).f1 12892 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12892 164 ∧
    0 ≤ (tableEnvelope C).w1 12892 164 ∧ 0 ≤ (tableEnvelope C).w2 12892 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12892 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12892 164 ∧ 0 ≤ d.f1 12892 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12892 164 ∧ 0 ≤ d.w1 12892 164 ∧ 0 ≤ d.w2 12892 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12892 ≤ 2 * (228 / 100 : ℝ) / 12892 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12892 ≤ 2 * (370 / 100 : ℝ) / 12892 := by
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
    (completeRAData (tableEnvelope C) 12892 164).locationBound 12892 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12892 164).energyBound 12892 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12892 164) (d.f1 12892 164) d.f2 ≤
      32 * (((551745907 / 125000000000000000) : ℝ) + (1472574263 / 1000000000000000000) + (353933801 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12892 164) (d.w1 12892 164)
      (d.w2 12892 164) ≤
      32 * (((1752503409 / 100000000000000000000) : ℝ) + (38964773 / 3125000000000000000) + (227787821 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12892 164) (d.f1 12892 164) d.f2 ≤
      ((551745907 / 125000000000000000) : ℝ) ^ 2 + 2 * ((551745907 / 125000000000000000)) * ((1472574263 / 1000000000000000000)) * (126 / 100) +
      2 * (((1472574263 / 1000000000000000000)) ^ 2 + 2 * ((551745907 / 125000000000000000)) * ((353933801 / 1000000000000000000))) +
      6 * ((1472574263 / 1000000000000000000)) * ((353933801 / 1000000000000000000)) * (126 / 100) + 8 * ((353933801 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12892 164) (d.f1 12892 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12892 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12892 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12892 164) (d.f1 12892 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12892 164) (d.w1 12892 164) (d.w2 12892 164)
  have hwexpr0 : 0 ≤ d.w0 12892 164 + d.w1 12892 164 * √(π / 2) +
      2 * d.w2 12892 164 + energyR16 12892 *
      radiusPolynomialRoot16 (d.w0 12892 164) (d.w1 12892 164) (d.w2 12892 164) := by
    positivity
  constructor
  · change (12892 : ℝ) ^ 8 * (mA 12892 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12892 164) (d.f1 12892 164) d.f2 + locationR16 12892 *
        radiusPolynomialRoot16 (d.f0 12892 164) (d.f1 12892 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12892 : ℝ) ^ 8 * (mA 12892 : ℝ) ^ 8 *
        ((((551745907 / 125000000000000000) : ℝ) ^ 2 + 2 * ((551745907 / 125000000000000000)) * ((1472574263 / 1000000000000000000)) * (126 / 100) +
          2 * (((1472574263 / 1000000000000000000)) ^ 2 + 2 * ((551745907 / 125000000000000000)) * ((353933801 / 1000000000000000000))) +
          6 * ((1472574263 / 1000000000000000000)) * ((353933801 / 1000000000000000000)) * (126 / 100) + 8 * ((353933801 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12892) *
          (32 * (((551745907 / 125000000000000000) : ℝ) + (1472574263 / 1000000000000000000) + (353933801 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12892 : ℝ) ^ 16 *
      (d.w0 12892 164 + d.w1 12892 164 * √(π / 2) + 2 * d.w2 12892 164 +
        energyR16 12892 * radiusPolynomialRoot16 (d.w0 12892 164) (d.w1 12892 164)
          (d.w2 12892 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12892 : ℝ) ^ 16 *
        (((1752503409 / 100000000000000000000) : ℝ) + ((38964773 / 3125000000000000000)) * (126 / 100) + 2 * ((227787821 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12892) *
          (32 * (((1752503409 / 100000000000000000000) : ℝ) + (38964773 / 3125000000000000000) + (227787821 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12892

/-! A coarse bound on the actual paper statistics constant at dimension 12893. -/
namespace BstLean.Part266.Row12893
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12891 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12891 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12891 128 ≤ (13145 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13145 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12893) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12893 : ℕ))
    (by norm_num : (12893 : ℕ) ≤ 16384)
  have ht : paperTail256 12893 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12893 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12893 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12893 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12893 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12893 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12891 128 * √(2 / (12893 : ℝ)) *
      (√(12893 : ℝ) + paperT0 12893 + paperTail256 12893) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12893 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12893 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12893 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12891 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12891 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12893 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12893

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12893
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12893 (61 / 100) 164 (17 / (100 * 12893)) (26 / (10 * 12893)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12893 (61 / 100) 164 (17 / (100 * 12893)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (227732623 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (282612427 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4532590673 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12893 / 12893 * (61 / 100)) ^ 4 * inverseRadius8 (12893 - 1) /
            envelopeGap 12893 (61 / 100) 164 (17 / (100 * 12893)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12893

namespace BstLean.Part266.Row12893
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12893 164 ≤ (4413111971 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12893 164 ≤ (1472288863 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (88466297 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12893 164 ≤ (1752095761 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12893 164 ≤ (1246582673 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12893 164 ≤ (455469637 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (227732623 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (227732623 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (282612427 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4532590673 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3631177 / 1000000000) : ℝ) ≤ √(17 / (100 * 12893) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12893) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (266770397 / 125000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7518143747 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12893) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12893) ≤ (685553 / 6250000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12893) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12893 * (164 : ℝ) ^ 2 + 26 / (10 * 12893) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12893) : ℝ)) (tA 12893 * 164 ^ 2 + 26 / (10 * 12893)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3631177 / 1000000000))) * ((227732623 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3631177 / 1000000000)) ^ 3) * ((282612427 / 200000000000000000000000))) + ((4532590673 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3631177 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12893) : ℝ)) d.D d.V d.P (√(tA 12893) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3631177 / 1000000000)) ^ 2 * (((266770397 / 125000000000000)) * ((7518143747 / 200000000000000000)))) + ((4532590673 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12893) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3631177 / 1000000000)) * ((227732623 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12893) : ℝ)) (tA 12893 * 164 ^ 2 + 26 / (10 * 12893)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((227732623 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3631177 / 1000000000)) ^ 2) * ((282612427 / 200000000000000000000000)) + ((4532590673 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12893) : ℝ)) (√(26 / (10 * 12893) : ℝ)) d.D d.V d.P (√(tA 12893) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3631177 / 1000000000)) * (((266770397 / 125000000000000)) * ((7518143747 / 200000000000000000))) + ((4532590673 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12893) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((227732623 / 50000000000000000000) : ℝ) + ((4532590673 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12893

namespace BstLean.Part266.Row12893
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12893 164 ∧
    0 ≤ (tableEnvelope C).f1 12893 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12893 164 ∧
    0 ≤ (tableEnvelope C).w1 12893 164 ∧ 0 ≤ (tableEnvelope C).w2 12893 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12893 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12893 164 ∧ 0 ≤ d.f1 12893 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12893 164 ∧ 0 ≤ d.w1 12893 164 ∧ 0 ≤ d.w2 12893 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12893 ≤ 2 * (228 / 100 : ℝ) / 12893 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12893 ≤ 2 * (370 / 100 : ℝ) / 12893 := by
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
    (completeRAData (tableEnvelope C) 12893 164).locationBound 12893 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12893 164).energyBound 12893 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12893 164) (d.f1 12893 164) d.f2 ≤
      32 * (((4413111971 / 1000000000000000000) : ℝ) + (1472288863 / 1000000000000000000) + (88466297 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12893 164) (d.w1 12893 164)
      (d.w2 12893 164) ≤
      32 * (((1752095761 / 100000000000000000000) : ℝ) + (1246582673 / 100000000000000000000) + (455469637 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12893 164) (d.f1 12893 164) d.f2 ≤
      ((4413111971 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4413111971 / 1000000000000000000)) * ((1472288863 / 1000000000000000000)) * (126 / 100) +
      2 * (((1472288863 / 1000000000000000000)) ^ 2 + 2 * ((4413111971 / 1000000000000000000)) * ((88466297 / 250000000000000000))) +
      6 * ((1472288863 / 1000000000000000000)) * ((88466297 / 250000000000000000)) * (126 / 100) + 8 * ((88466297 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12893 164) (d.f1 12893 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12893 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12893 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12893 164) (d.f1 12893 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12893 164) (d.w1 12893 164) (d.w2 12893 164)
  have hwexpr0 : 0 ≤ d.w0 12893 164 + d.w1 12893 164 * √(π / 2) +
      2 * d.w2 12893 164 + energyR16 12893 *
      radiusPolynomialRoot16 (d.w0 12893 164) (d.w1 12893 164) (d.w2 12893 164) := by
    positivity
  constructor
  · change (12893 : ℝ) ^ 8 * (mA 12893 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12893 164) (d.f1 12893 164) d.f2 + locationR16 12893 *
        radiusPolynomialRoot16 (d.f0 12893 164) (d.f1 12893 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12893 : ℝ) ^ 8 * (mA 12893 : ℝ) ^ 8 *
        ((((4413111971 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4413111971 / 1000000000000000000)) * ((1472288863 / 1000000000000000000)) * (126 / 100) +
          2 * (((1472288863 / 1000000000000000000)) ^ 2 + 2 * ((4413111971 / 1000000000000000000)) * ((88466297 / 250000000000000000))) +
          6 * ((1472288863 / 1000000000000000000)) * ((88466297 / 250000000000000000)) * (126 / 100) + 8 * ((88466297 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12893) *
          (32 * (((4413111971 / 1000000000000000000) : ℝ) + (1472288863 / 1000000000000000000) + (88466297 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12893 : ℝ) ^ 16 *
      (d.w0 12893 164 + d.w1 12893 164 * √(π / 2) + 2 * d.w2 12893 164 +
        energyR16 12893 * radiusPolynomialRoot16 (d.w0 12893 164) (d.w1 12893 164)
          (d.w2 12893 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12893 : ℝ) ^ 16 *
        (((1752095761 / 100000000000000000000) : ℝ) + ((1246582673 / 100000000000000000000)) * (126 / 100) + 2 * ((455469637 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12893) *
          (32 * (((1752095761 / 100000000000000000000) : ℝ) + (1246582673 / 100000000000000000000) + (455469637 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12893

/-! A coarse bound on the actual paper statistics constant at dimension 12894. -/
namespace BstLean.Part266.Row12894
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12892 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12892 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12892 128 ≤ (13146 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13146 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12894) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12894 : ℕ))
    (by norm_num : (12894 : ℕ) ≤ 16384)
  have ht : paperTail256 12894 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12894 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12894 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12894 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12894 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12894 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12892 128 * √(2 / (12894 : ℝ)) *
      (√(12894 : ℝ) + paperT0 12894 + paperTail256 12894) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12894 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12894 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12894 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12892 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12892 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12894 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12894

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12894
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12894 (61 / 100) 164 (17 / (100 * 12894)) (26 / (10 * 12894)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12894 (61 / 100) 164 (17 / (100 * 12894)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (227679639 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1412623807 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4529752331 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12894 / 12894 * (61 / 100)) ^ 4 * inverseRadius8 (12894 - 1) /
            envelopeGap 12894 (61 / 100) 164 (17 / (100 * 12894)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12894

namespace BstLean.Part266.Row12894
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12894 164 ≤ (4412256979 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12894 164 ≤ (368000889 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (353796597 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12894 164 ≤ (1751688253 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12894 164 ≤ (1246292709 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12894 164 ≤ (227681833 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (227679639 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (227679639 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1412623807 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4529752331 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((907759 / 250000000) : ℝ) ≤ √(17 / (100 * 12894) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12894) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (133369681 / 62500000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18792444007 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12894) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12894) ≤ (109679973 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12894) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12894 * (164 : ℝ) ^ 2 + 26 / (10 * 12894) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12894) : ℝ)) (tA 12894 * 164 ^ 2 + 26 / (10 * 12894)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((907759 / 250000000))) * ((227679639 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((907759 / 250000000)) ^ 3) * ((1412623807 / 1000000000000000000000000))) + ((4529752331 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((907759 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12894) : ℝ)) d.D d.V d.P (√(tA 12894) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((907759 / 250000000)) ^ 2 * (((133369681 / 62500000000000)) * ((18792444007 / 500000000000000000)))) + ((4529752331 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12894) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((907759 / 250000000)) * ((227679639 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12894) : ℝ)) (tA 12894 * 164 ^ 2 + 26 / (10 * 12894)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((227679639 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((907759 / 250000000)) ^ 2) * ((1412623807 / 1000000000000000000000000)) + ((4529752331 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12894) : ℝ)) (√(26 / (10 * 12894) : ℝ)) d.D d.V d.P (√(tA 12894) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((907759 / 250000000)) * (((133369681 / 62500000000000)) * ((18792444007 / 500000000000000000))) + ((4529752331 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12894) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((227679639 / 50000000000000000000) : ℝ) + ((4529752331 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12894

namespace BstLean.Part266.Row12894
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12894 164 ∧
    0 ≤ (tableEnvelope C).f1 12894 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12894 164 ∧
    0 ≤ (tableEnvelope C).w1 12894 164 ∧ 0 ≤ (tableEnvelope C).w2 12894 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12894 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12894 164 ∧ 0 ≤ d.f1 12894 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12894 164 ∧ 0 ≤ d.w1 12894 164 ∧ 0 ≤ d.w2 12894 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12894 ≤ 2 * (228 / 100 : ℝ) / 12894 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12894 ≤ 2 * (370 / 100 : ℝ) / 12894 := by
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
    (completeRAData (tableEnvelope C) 12894 164).locationBound 12894 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12894 164).energyBound 12894 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12894 164) (d.f1 12894 164) d.f2 ≤
      32 * (((4412256979 / 1000000000000000000) : ℝ) + (368000889 / 250000000000000000) + (353796597 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12894 164) (d.w1 12894 164)
      (d.w2 12894 164) ≤
      32 * (((1751688253 / 100000000000000000000) : ℝ) + (1246292709 / 100000000000000000000) + (227681833 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12894 164) (d.f1 12894 164) d.f2 ≤
      ((4412256979 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4412256979 / 1000000000000000000)) * ((368000889 / 250000000000000000)) * (126 / 100) +
      2 * (((368000889 / 250000000000000000)) ^ 2 + 2 * ((4412256979 / 1000000000000000000)) * ((353796597 / 1000000000000000000))) +
      6 * ((368000889 / 250000000000000000)) * ((353796597 / 1000000000000000000)) * (126 / 100) + 8 * ((353796597 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12894 164) (d.f1 12894 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12894 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12894 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12894 164) (d.f1 12894 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12894 164) (d.w1 12894 164) (d.w2 12894 164)
  have hwexpr0 : 0 ≤ d.w0 12894 164 + d.w1 12894 164 * √(π / 2) +
      2 * d.w2 12894 164 + energyR16 12894 *
      radiusPolynomialRoot16 (d.w0 12894 164) (d.w1 12894 164) (d.w2 12894 164) := by
    positivity
  constructor
  · change (12894 : ℝ) ^ 8 * (mA 12894 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12894 164) (d.f1 12894 164) d.f2 + locationR16 12894 *
        radiusPolynomialRoot16 (d.f0 12894 164) (d.f1 12894 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12894 : ℝ) ^ 8 * (mA 12894 : ℝ) ^ 8 *
        ((((4412256979 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4412256979 / 1000000000000000000)) * ((368000889 / 250000000000000000)) * (126 / 100) +
          2 * (((368000889 / 250000000000000000)) ^ 2 + 2 * ((4412256979 / 1000000000000000000)) * ((353796597 / 1000000000000000000))) +
          6 * ((368000889 / 250000000000000000)) * ((353796597 / 1000000000000000000)) * (126 / 100) + 8 * ((353796597 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12894) *
          (32 * (((4412256979 / 1000000000000000000) : ℝ) + (368000889 / 250000000000000000) + (353796597 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12894 : ℝ) ^ 16 *
      (d.w0 12894 164 + d.w1 12894 164 * √(π / 2) + 2 * d.w2 12894 164 +
        energyR16 12894 * radiusPolynomialRoot16 (d.w0 12894 164) (d.w1 12894 164)
          (d.w2 12894 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12894 : ℝ) ^ 16 *
        (((1751688253 / 100000000000000000000) : ℝ) + ((1246292709 / 100000000000000000000)) * (126 / 100) + 2 * ((227681833 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12894) *
          (32 * (((1751688253 / 100000000000000000000) : ℝ) + (1246292709 / 100000000000000000000) + (227681833 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12894

/-! A coarse bound on the actual paper statistics constant at dimension 12895. -/
namespace BstLean.Part266.Row12895
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12893 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12893 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12893 128 ≤ (13147 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13147 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12895) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12895 : ℕ))
    (by norm_num : (12895 : ℕ) ≤ 16384)
  have ht : paperTail256 12895 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12895 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12895 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12895 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12895 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12895 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12893 128 * √(2 / (12895 : ℝ)) *
      (√(12895 : ℝ) + paperT0 12895 + paperTail256 12895) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12895 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12895 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12895 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12893 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12893 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12895 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12895

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12895
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12895 (61 / 100) 164 (17 / (100 * 12895)) (26 / (10 * 12895)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12895 (61 / 100) 164 (17 / (100 * 12895)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (227626671 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (88261603 / 62500000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (452691599 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12895 / 12895 * (61 / 100)) ^ 4 * inverseRadius8 (12895 - 1) /
            envelopeGap 12895 (61 / 100) 164 (17 / (100 * 12895)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12895

namespace BstLean.Part266.Row12895
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12895 164 ≤ (4411402273 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12895 164 ≤ (735859169 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (44216003 / 125000000000000000)
  w0 : (tableEnvelope C).w0 12895 164 ≤ (875640441 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12895 164 ≤ (623001419 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12895 164 ≤ (3556701 / 781250000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (227626671 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (227626671 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (88261603 / 62500000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (452691599 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((726179 / 200000000) : ℝ) ≤ √(17 / (100 * 12895) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12895) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2133666661 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37579058637 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12895) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12895) ≤ (109671467 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12895) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12895 * (164 : ℝ) ^ 2 + 26 / (10 * 12895) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12895) : ℝ)) (tA 12895 * 164 ^ 2 + 26 / (10 * 12895)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((726179 / 200000000))) * ((227626671 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((726179 / 200000000)) ^ 3) * ((88261603 / 62500000000000000000000))) + ((452691599 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((726179 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12895) : ℝ)) d.D d.V d.P (√(tA 12895) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((726179 / 200000000)) ^ 2 * (((2133666661 / 1000000000000000)) * ((37579058637 / 1000000000000000000)))) + ((452691599 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12895) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((726179 / 200000000)) * ((227626671 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12895) : ℝ)) (tA 12895 * 164 ^ 2 + 26 / (10 * 12895)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((227626671 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((726179 / 200000000)) ^ 2) * ((88261603 / 62500000000000000000000)) + ((452691599 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12895) : ℝ)) (√(26 / (10 * 12895) : ℝ)) d.D d.V d.P (√(tA 12895) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((726179 / 200000000)) * (((2133666661 / 1000000000000000)) * ((37579058637 / 1000000000000000000))) + ((452691599 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12895) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((227626671 / 50000000000000000000) : ℝ) + ((452691599 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12895

namespace BstLean.Part266.Row12895
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12895 164 ∧
    0 ≤ (tableEnvelope C).f1 12895 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12895 164 ∧
    0 ≤ (tableEnvelope C).w1 12895 164 ∧ 0 ≤ (tableEnvelope C).w2 12895 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12895 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12895 164 ∧ 0 ≤ d.f1 12895 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12895 164 ∧ 0 ≤ d.w1 12895 164 ∧ 0 ≤ d.w2 12895 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12895 ≤ 2 * (228 / 100 : ℝ) / 12895 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12895 ≤ 2 * (370 / 100 : ℝ) / 12895 := by
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
    (completeRAData (tableEnvelope C) 12895 164).locationBound 12895 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12895 164).energyBound 12895 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12895 164) (d.f1 12895 164) d.f2 ≤
      32 * (((4411402273 / 1000000000000000000) : ℝ) + (735859169 / 500000000000000000) + (44216003 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12895 164) (d.w1 12895 164)
      (d.w2 12895 164) ≤
      32 * (((875640441 / 50000000000000000000) : ℝ) + (623001419 / 50000000000000000000) + (3556701 / 781250000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12895 164) (d.f1 12895 164) d.f2 ≤
      ((4411402273 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4411402273 / 1000000000000000000)) * ((735859169 / 500000000000000000)) * (126 / 100) +
      2 * (((735859169 / 500000000000000000)) ^ 2 + 2 * ((4411402273 / 1000000000000000000)) * ((44216003 / 125000000000000000))) +
      6 * ((735859169 / 500000000000000000)) * ((44216003 / 125000000000000000)) * (126 / 100) + 8 * ((44216003 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12895 164) (d.f1 12895 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12895 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12895 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12895 164) (d.f1 12895 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12895 164) (d.w1 12895 164) (d.w2 12895 164)
  have hwexpr0 : 0 ≤ d.w0 12895 164 + d.w1 12895 164 * √(π / 2) +
      2 * d.w2 12895 164 + energyR16 12895 *
      radiusPolynomialRoot16 (d.w0 12895 164) (d.w1 12895 164) (d.w2 12895 164) := by
    positivity
  constructor
  · change (12895 : ℝ) ^ 8 * (mA 12895 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12895 164) (d.f1 12895 164) d.f2 + locationR16 12895 *
        radiusPolynomialRoot16 (d.f0 12895 164) (d.f1 12895 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12895 : ℝ) ^ 8 * (mA 12895 : ℝ) ^ 8 *
        ((((4411402273 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4411402273 / 1000000000000000000)) * ((735859169 / 500000000000000000)) * (126 / 100) +
          2 * (((735859169 / 500000000000000000)) ^ 2 + 2 * ((4411402273 / 1000000000000000000)) * ((44216003 / 125000000000000000))) +
          6 * ((735859169 / 500000000000000000)) * ((44216003 / 125000000000000000)) * (126 / 100) + 8 * ((44216003 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12895) *
          (32 * (((4411402273 / 1000000000000000000) : ℝ) + (735859169 / 500000000000000000) + (44216003 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12895 : ℝ) ^ 16 *
      (d.w0 12895 164 + d.w1 12895 164 * √(π / 2) + 2 * d.w2 12895 164 +
        energyR16 12895 * radiusPolynomialRoot16 (d.w0 12895 164) (d.w1 12895 164)
          (d.w2 12895 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12895 : ℝ) ^ 16 *
        (((875640441 / 50000000000000000000) : ℝ) + ((623001419 / 50000000000000000000)) * (126 / 100) + 2 * ((3556701 / 781250000000000000)) +
          (2 * (370 / 100 : ℝ) / 12895) *
          (32 * (((875640441 / 50000000000000000000) : ℝ) + (623001419 / 50000000000000000000) + (3556701 / 781250000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12895

/-! A coarse bound on the actual paper statistics constant at dimension 12896. -/
namespace BstLean.Part266.Row12896
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12894 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12894 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12894 128 ≤ (13148 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13148 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12896) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12896 : ℕ))
    (by norm_num : (12896 : ℕ) ≤ 16384)
  have ht : paperTail256 12896 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12896 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12896 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12896 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12896 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12896 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12894 128 * √(2 / (12896 : ℝ)) *
      (√(12896 : ℝ) + paperT0 12896 + paperTail256 12896) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12896 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12896 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12896 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12894 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12894 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12896 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12896

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12896
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12896 (61 / 100) 164 (17 / (100 * 12896)) (26 / (10 * 12896)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12896 (61 / 100) 164 (17 / (100 * 12896)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (455147439 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1411747659 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4524081649 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12896 / 12896 * (61 / 100)) ^ 4 * inverseRadius8 (12896 - 1) /
            envelopeGap 12896 (61 / 100) 164 (17 / (100 * 12896)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12896

namespace BstLean.Part266.Row12896
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12896 164 ≤ (88210887 / 20000000000000000)
  f1 : (tableEnvelope C).f1 12896 164 ≤ (3678581 / 2500000000000000)
  f2 : (tableEnvelope C).f2 ≤ (113171 / 320000000000000)
  w0 : (tableEnvelope C).w0 12896 164 ≤ (350174587 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12896 164 ≤ (15571409 / 1250000000000000000)
  w2 : (tableEnvelope C).w2 12896 164 ≤ (227575911 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (455147439 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (455147439 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1411747659 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4524081649 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((726151 / 200000000) : ℝ) ≤ √(17 / (100 * 12896) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12896) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (533354619 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18786615309 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12896) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12896) ≤ (109662963 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12896) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12896 * (164 : ℝ) ^ 2 + 26 / (10 * 12896) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12896) : ℝ)) (tA 12896 * 164 ^ 2 + 26 / (10 * 12896)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((726151 / 200000000))) * ((455147439 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((726151 / 200000000)) ^ 3) * ((1411747659 / 1000000000000000000000000))) + ((4524081649 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((726151 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12896) : ℝ)) d.D d.V d.P (√(tA 12896) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((726151 / 200000000)) ^ 2 * (((533354619 / 250000000000000)) * ((18786615309 / 500000000000000000)))) + ((4524081649 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12896) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((726151 / 200000000)) * ((455147439 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12896) : ℝ)) (tA 12896 * 164 ^ 2 + 26 / (10 * 12896)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((455147439 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((726151 / 200000000)) ^ 2) * ((1411747659 / 1000000000000000000000000)) + ((4524081649 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12896) : ℝ)) (√(26 / (10 * 12896) : ℝ)) d.D d.V d.P (√(tA 12896) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((726151 / 200000000)) * (((533354619 / 250000000000000)) * ((18786615309 / 500000000000000000))) + ((4524081649 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12896) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((455147439 / 100000000000000000000) : ℝ) + ((4524081649 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12896

namespace BstLean.Part266.Row12896
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12896 164 ∧
    0 ≤ (tableEnvelope C).f1 12896 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12896 164 ∧
    0 ≤ (tableEnvelope C).w1 12896 164 ∧ 0 ≤ (tableEnvelope C).w2 12896 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12896 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12896 164 ∧ 0 ≤ d.f1 12896 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12896 164 ∧ 0 ≤ d.w1 12896 164 ∧ 0 ≤ d.w2 12896 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12896 ≤ 2 * (228 / 100 : ℝ) / 12896 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12896 ≤ 2 * (370 / 100 : ℝ) / 12896 := by
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
    (completeRAData (tableEnvelope C) 12896 164).locationBound 12896 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12896 164).energyBound 12896 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12896 164) (d.f1 12896 164) d.f2 ≤
      32 * (((88210887 / 20000000000000000) : ℝ) + (3678581 / 2500000000000000) + (113171 / 320000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12896 164) (d.w1 12896 164)
      (d.w2 12896 164) ≤
      32 * (((350174587 / 20000000000000000000) : ℝ) + (15571409 / 1250000000000000000) + (227575911 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12896 164) (d.f1 12896 164) d.f2 ≤
      ((88210887 / 20000000000000000) : ℝ) ^ 2 + 2 * ((88210887 / 20000000000000000)) * ((3678581 / 2500000000000000)) * (126 / 100) +
      2 * (((3678581 / 2500000000000000)) ^ 2 + 2 * ((88210887 / 20000000000000000)) * ((113171 / 320000000000000))) +
      6 * ((3678581 / 2500000000000000)) * ((113171 / 320000000000000)) * (126 / 100) + 8 * ((113171 / 320000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12896 164) (d.f1 12896 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12896 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12896 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12896 164) (d.f1 12896 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12896 164) (d.w1 12896 164) (d.w2 12896 164)
  have hwexpr0 : 0 ≤ d.w0 12896 164 + d.w1 12896 164 * √(π / 2) +
      2 * d.w2 12896 164 + energyR16 12896 *
      radiusPolynomialRoot16 (d.w0 12896 164) (d.w1 12896 164) (d.w2 12896 164) := by
    positivity
  constructor
  · change (12896 : ℝ) ^ 8 * (mA 12896 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12896 164) (d.f1 12896 164) d.f2 + locationR16 12896 *
        radiusPolynomialRoot16 (d.f0 12896 164) (d.f1 12896 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12896 : ℝ) ^ 8 * (mA 12896 : ℝ) ^ 8 *
        ((((88210887 / 20000000000000000) : ℝ) ^ 2 + 2 * ((88210887 / 20000000000000000)) * ((3678581 / 2500000000000000)) * (126 / 100) +
          2 * (((3678581 / 2500000000000000)) ^ 2 + 2 * ((88210887 / 20000000000000000)) * ((113171 / 320000000000000))) +
          6 * ((3678581 / 2500000000000000)) * ((113171 / 320000000000000)) * (126 / 100) + 8 * ((113171 / 320000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12896) *
          (32 * (((88210887 / 20000000000000000) : ℝ) + (3678581 / 2500000000000000) + (113171 / 320000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12896 : ℝ) ^ 16 *
      (d.w0 12896 164 + d.w1 12896 164 * √(π / 2) + 2 * d.w2 12896 164 +
        energyR16 12896 * radiusPolynomialRoot16 (d.w0 12896 164) (d.w1 12896 164)
          (d.w2 12896 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12896 : ℝ) ^ 16 *
        (((350174587 / 20000000000000000000) : ℝ) + ((15571409 / 1250000000000000000)) * (126 / 100) + 2 * ((227575911 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12896) *
          (32 * (((350174587 / 20000000000000000000) : ℝ) + (15571409 / 1250000000000000000) + (227575911 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12896

/-! A coarse bound on the actual paper statistics constant at dimension 12897. -/
namespace BstLean.Part266.Row12897
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12895 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12895 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12895 128 ≤ (13149 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13149 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12897) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12897 : ℕ))
    (by norm_num : (12897 : ℕ) ≤ 16384)
  have ht : paperTail256 12897 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12897 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12897 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12897 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12897 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12897 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12895 128 * √(2 / (12897 : ℝ)) *
      (√(12897 : ℝ) + paperT0 12897 + paperTail256 12897) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12897 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12897 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12897 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12895 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12895 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12897 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12897

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12897
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12897 (61 / 100) 164 (17 / (100 * 12897)) (26 / (10 * 12897)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12897 (61 / 100) 164 (17 / (100 * 12897)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (455041569 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (17641373 / 12500000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4521249307 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12897 / 12897 * (61 / 100)) ^ 4 * inverseRadius8 (12897 - 1) /
            envelopeGap 12897 (61 / 100) 164 (17 / (100 * 12897)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12897

namespace BstLean.Part266.Row12897
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12897 164 ≤ (275605639 / 62500000000000000)
  f1 : (tableEnvelope C).f1 12897 164 ≤ (367786841 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (353590843 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12897 164 ≤ (1750465841 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12897 164 ≤ (1245423041 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12897 164 ≤ (455045949 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (455041569 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (455041569 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (17641373 / 12500000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4521249307 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1815307 / 500000000) : ℝ) ≤ √(17 / (100 * 12897) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12897) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1066585169 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37567403957 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12897) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12897) ≤ (5482723 / 50000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12897) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12897 * (164 : ℝ) ^ 2 + 26 / (10 * 12897) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12897) : ℝ)) (tA 12897 * 164 ^ 2 + 26 / (10 * 12897)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1815307 / 500000000))) * ((455041569 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1815307 / 500000000)) ^ 3) * ((17641373 / 12500000000000000000000))) + ((4521249307 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1815307 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12897) : ℝ)) d.D d.V d.P (√(tA 12897) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1815307 / 500000000)) ^ 2 * (((1066585169 / 500000000000000)) * ((37567403957 / 1000000000000000000)))) + ((4521249307 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12897) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1815307 / 500000000)) * ((455041569 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12897) : ℝ)) (tA 12897 * 164 ^ 2 + 26 / (10 * 12897)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((455041569 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1815307 / 500000000)) ^ 2) * ((17641373 / 12500000000000000000000)) + ((4521249307 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12897) : ℝ)) (√(26 / (10 * 12897) : ℝ)) d.D d.V d.P (√(tA 12897) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1815307 / 500000000)) * (((1066585169 / 500000000000000)) * ((37567403957 / 1000000000000000000))) + ((4521249307 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12897) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((455041569 / 100000000000000000000) : ℝ) + ((4521249307 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12897

namespace BstLean.Part266.Row12897
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12897 164 ∧
    0 ≤ (tableEnvelope C).f1 12897 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12897 164 ∧
    0 ≤ (tableEnvelope C).w1 12897 164 ∧ 0 ≤ (tableEnvelope C).w2 12897 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12897 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12897 164 ∧ 0 ≤ d.f1 12897 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12897 164 ∧ 0 ≤ d.w1 12897 164 ∧ 0 ≤ d.w2 12897 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12897 ≤ 2 * (228 / 100 : ℝ) / 12897 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12897 ≤ 2 * (370 / 100 : ℝ) / 12897 := by
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
    (completeRAData (tableEnvelope C) 12897 164).locationBound 12897 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12897 164).energyBound 12897 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12897 164) (d.f1 12897 164) d.f2 ≤
      32 * (((275605639 / 62500000000000000) : ℝ) + (367786841 / 250000000000000000) + (353590843 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12897 164) (d.w1 12897 164)
      (d.w2 12897 164) ≤
      32 * (((1750465841 / 100000000000000000000) : ℝ) + (1245423041 / 100000000000000000000) + (455045949 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12897 164) (d.f1 12897 164) d.f2 ≤
      ((275605639 / 62500000000000000) : ℝ) ^ 2 + 2 * ((275605639 / 62500000000000000)) * ((367786841 / 250000000000000000)) * (126 / 100) +
      2 * (((367786841 / 250000000000000000)) ^ 2 + 2 * ((275605639 / 62500000000000000)) * ((353590843 / 1000000000000000000))) +
      6 * ((367786841 / 250000000000000000)) * ((353590843 / 1000000000000000000)) * (126 / 100) + 8 * ((353590843 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12897 164) (d.f1 12897 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12897 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12897 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12897 164) (d.f1 12897 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12897 164) (d.w1 12897 164) (d.w2 12897 164)
  have hwexpr0 : 0 ≤ d.w0 12897 164 + d.w1 12897 164 * √(π / 2) +
      2 * d.w2 12897 164 + energyR16 12897 *
      radiusPolynomialRoot16 (d.w0 12897 164) (d.w1 12897 164) (d.w2 12897 164) := by
    positivity
  constructor
  · change (12897 : ℝ) ^ 8 * (mA 12897 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12897 164) (d.f1 12897 164) d.f2 + locationR16 12897 *
        radiusPolynomialRoot16 (d.f0 12897 164) (d.f1 12897 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12897 : ℝ) ^ 8 * (mA 12897 : ℝ) ^ 8 *
        ((((275605639 / 62500000000000000) : ℝ) ^ 2 + 2 * ((275605639 / 62500000000000000)) * ((367786841 / 250000000000000000)) * (126 / 100) +
          2 * (((367786841 / 250000000000000000)) ^ 2 + 2 * ((275605639 / 62500000000000000)) * ((353590843 / 1000000000000000000))) +
          6 * ((367786841 / 250000000000000000)) * ((353590843 / 1000000000000000000)) * (126 / 100) + 8 * ((353590843 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12897) *
          (32 * (((275605639 / 62500000000000000) : ℝ) + (367786841 / 250000000000000000) + (353590843 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12897 : ℝ) ^ 16 *
      (d.w0 12897 164 + d.w1 12897 164 * √(π / 2) + 2 * d.w2 12897 164 +
        energyR16 12897 * radiusPolynomialRoot16 (d.w0 12897 164) (d.w1 12897 164)
          (d.w2 12897 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12897 : ℝ) ^ 16 *
        (((1750465841 / 100000000000000000000) : ℝ) + ((1245423041 / 100000000000000000000)) * (126 / 100) + 2 * ((455045949 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12897) *
          (32 * (((1750465841 / 100000000000000000000) : ℝ) + (1245423041 / 100000000000000000000) + (455045949 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12897

/-! A coarse bound on the actual paper statistics constant at dimension 12898. -/
namespace BstLean.Part266.Row12898
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12896 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12896 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12896 128 ≤ (13150 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13150 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12898) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12898 : ℕ))
    (by norm_num : (12898 : ℕ) ≤ 16384)
  have ht : paperTail256 12898 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12898 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12898 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12898 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12898 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12898 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12896 128 * √(2 / (12898 : ℝ)) *
      (√(12898 : ℝ) + paperT0 12898 + paperTail256 12898) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12898 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12898 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12898 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12896 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12896 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12898 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12898

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12898
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12898 (61 / 100) 164 (17 / (100 * 12898)) (26 / (10 * 12898)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12898 (61 / 100) 164 (17 / (100 * 12898)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (113733933 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1410872191 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4518418961 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12898 / 12898 * (61 / 100)) ^ 4 * inverseRadius8 (12898 - 1) /
            envelopeGap 12898 (61 / 100) 164 (17 / (100 * 12898)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12898

namespace BstLean.Part266.Row12898
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12898 164 ≤ (4408836389 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12898 164 ≤ (1470862419 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (88380583 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12898 164 ≤ (350011777 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12898 164 ≤ (1245133457 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12898 164 ≤ (454940109 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (113733933 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (113733933 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1410872191 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4518418961 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3630473 / 1000000000) : ℝ) ≤ √(17 / (100 * 12898) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12898) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2132922249 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7512315731 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12898) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12898) ≤ (54822979 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12898) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12898 * (164 : ℝ) ^ 2 + 26 / (10 * 12898) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12898) : ℝ)) (tA 12898 * 164 ^ 2 + 26 / (10 * 12898)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3630473 / 1000000000))) * ((113733933 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3630473 / 1000000000)) ^ 3) * ((1410872191 / 1000000000000000000000000))) + ((4518418961 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3630473 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12898) : ℝ)) d.D d.V d.P (√(tA 12898) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3630473 / 1000000000)) ^ 2 * (((2132922249 / 1000000000000000)) * ((7512315731 / 200000000000000000)))) + ((4518418961 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12898) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3630473 / 1000000000)) * ((113733933 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12898) : ℝ)) (tA 12898 * 164 ^ 2 + 26 / (10 * 12898)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((113733933 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3630473 / 1000000000)) ^ 2) * ((1410872191 / 1000000000000000000000000)) + ((4518418961 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12898) : ℝ)) (√(26 / (10 * 12898) : ℝ)) d.D d.V d.P (√(tA 12898) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3630473 / 1000000000)) * (((2132922249 / 1000000000000000)) * ((7512315731 / 200000000000000000))) + ((4518418961 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12898) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((113733933 / 25000000000000000000) : ℝ) + ((4518418961 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12898

namespace BstLean.Part266.Row12898
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12898 164 ∧
    0 ≤ (tableEnvelope C).f1 12898 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12898 164 ∧
    0 ≤ (tableEnvelope C).w1 12898 164 ∧ 0 ≤ (tableEnvelope C).w2 12898 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12898 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12898 164 ∧ 0 ≤ d.f1 12898 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12898 164 ∧ 0 ≤ d.w1 12898 164 ∧ 0 ≤ d.w2 12898 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12898 ≤ 2 * (228 / 100 : ℝ) / 12898 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12898 ≤ 2 * (370 / 100 : ℝ) / 12898 := by
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
    (completeRAData (tableEnvelope C) 12898 164).locationBound 12898 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12898 164).energyBound 12898 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12898 164) (d.f1 12898 164) d.f2 ≤
      32 * (((4408836389 / 1000000000000000000) : ℝ) + (1470862419 / 1000000000000000000) + (88380583 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12898 164) (d.w1 12898 164)
      (d.w2 12898 164) ≤
      32 * (((350011777 / 20000000000000000000) : ℝ) + (1245133457 / 100000000000000000000) + (454940109 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12898 164) (d.f1 12898 164) d.f2 ≤
      ((4408836389 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4408836389 / 1000000000000000000)) * ((1470862419 / 1000000000000000000)) * (126 / 100) +
      2 * (((1470862419 / 1000000000000000000)) ^ 2 + 2 * ((4408836389 / 1000000000000000000)) * ((88380583 / 250000000000000000))) +
      6 * ((1470862419 / 1000000000000000000)) * ((88380583 / 250000000000000000)) * (126 / 100) + 8 * ((88380583 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12898 164) (d.f1 12898 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12898 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12898 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12898 164) (d.f1 12898 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12898 164) (d.w1 12898 164) (d.w2 12898 164)
  have hwexpr0 : 0 ≤ d.w0 12898 164 + d.w1 12898 164 * √(π / 2) +
      2 * d.w2 12898 164 + energyR16 12898 *
      radiusPolynomialRoot16 (d.w0 12898 164) (d.w1 12898 164) (d.w2 12898 164) := by
    positivity
  constructor
  · change (12898 : ℝ) ^ 8 * (mA 12898 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12898 164) (d.f1 12898 164) d.f2 + locationR16 12898 *
        radiusPolynomialRoot16 (d.f0 12898 164) (d.f1 12898 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12898 : ℝ) ^ 8 * (mA 12898 : ℝ) ^ 8 *
        ((((4408836389 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4408836389 / 1000000000000000000)) * ((1470862419 / 1000000000000000000)) * (126 / 100) +
          2 * (((1470862419 / 1000000000000000000)) ^ 2 + 2 * ((4408836389 / 1000000000000000000)) * ((88380583 / 250000000000000000))) +
          6 * ((1470862419 / 1000000000000000000)) * ((88380583 / 250000000000000000)) * (126 / 100) + 8 * ((88380583 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12898) *
          (32 * (((4408836389 / 1000000000000000000) : ℝ) + (1470862419 / 1000000000000000000) + (88380583 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12898 : ℝ) ^ 16 *
      (d.w0 12898 164 + d.w1 12898 164 * √(π / 2) + 2 * d.w2 12898 164 +
        energyR16 12898 * radiusPolynomialRoot16 (d.w0 12898 164) (d.w1 12898 164)
          (d.w2 12898 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12898 : ℝ) ^ 16 *
        (((350011777 / 20000000000000000000) : ℝ) + ((1245133457 / 100000000000000000000)) * (126 / 100) + 2 * ((454940109 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12898) *
          (32 * (((350011777 / 20000000000000000000) : ℝ) + (1245133457 / 100000000000000000000) + (454940109 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12898

/-! A coarse bound on the actual paper statistics constant at dimension 12899. -/
namespace BstLean.Part266.Row12899
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12897 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12897 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12897 128 ≤ (13151 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13151 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12899) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12899 : ℕ))
    (by norm_num : (12899 : ℕ) ≤ 16384)
  have ht : paperTail256 12899 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12899 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12899 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12899 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12899 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12899 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12897 128 * √(2 / (12899 : ℝ)) *
      (√(12899 : ℝ) + paperT0 12899 + paperTail256 12899) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12899 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12899 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12899 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12897 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12897 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12899 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12899

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12899
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12899 (61 / 100) 164 (17 / (100 * 12899)) (26 / (10 * 12899)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12899 (61 / 100) 164 (17 / (100 * 12899)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (454829927 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1410434711 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4515590611 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12899 / 12899 * (61 / 100)) ^ 4 * inverseRadius8 (12899 - 1) /
            envelopeGap 12899 (61 / 100) 164 (17 / (100 * 12899)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12899

namespace BstLean.Part266.Row12899
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12899 164 ≤ (110199571 / 25000000000000000)
  f1 : (tableEnvelope C).f1 12899 164 ≤ (1470577563 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (4418173 / 12500000000000000)
  w0 : (tableEnvelope C).w0 12899 164 ≤ (349930413 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12899 164 ≤ (1244843969 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12899 164 ≤ (227417151 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (454829927 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (454829927 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1410434711 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4515590611 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((907583 / 250000000) : ℝ) ≤ √(17 / (100 * 12899) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12899) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2132674207 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37555754699 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12899) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12899) ≤ (54818729 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12899) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12899 * (164 : ℝ) ^ 2 + 26 / (10 * 12899) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12899) : ℝ)) (tA 12899 * 164 ^ 2 + 26 / (10 * 12899)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((907583 / 250000000))) * ((454829927 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((907583 / 250000000)) ^ 3) * ((1410434711 / 1000000000000000000000000))) + ((4515590611 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((907583 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12899) : ℝ)) d.D d.V d.P (√(tA 12899) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((907583 / 250000000)) ^ 2 * (((2132674207 / 1000000000000000)) * ((37555754699 / 1000000000000000000)))) + ((4515590611 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12899) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((907583 / 250000000)) * ((454829927 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12899) : ℝ)) (tA 12899 * 164 ^ 2 + 26 / (10 * 12899)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((454829927 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((907583 / 250000000)) ^ 2) * ((1410434711 / 1000000000000000000000000)) + ((4515590611 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12899) : ℝ)) (√(26 / (10 * 12899) : ℝ)) d.D d.V d.P (√(tA 12899) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((907583 / 250000000)) * (((2132674207 / 1000000000000000)) * ((37555754699 / 1000000000000000000))) + ((4515590611 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12899) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((454829927 / 100000000000000000000) : ℝ) + ((4515590611 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12899

namespace BstLean.Part266.Row12899
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12899 164 ∧
    0 ≤ (tableEnvelope C).f1 12899 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12899 164 ∧
    0 ≤ (tableEnvelope C).w1 12899 164 ∧ 0 ≤ (tableEnvelope C).w2 12899 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12899 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12899 164 ∧ 0 ≤ d.f1 12899 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12899 164 ∧ 0 ≤ d.w1 12899 164 ∧ 0 ≤ d.w2 12899 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12899 ≤ 2 * (228 / 100 : ℝ) / 12899 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12899 ≤ 2 * (370 / 100 : ℝ) / 12899 := by
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
    (completeRAData (tableEnvelope C) 12899 164).locationBound 12899 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12899 164).energyBound 12899 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12899 164) (d.f1 12899 164) d.f2 ≤
      32 * (((110199571 / 25000000000000000) : ℝ) + (1470577563 / 1000000000000000000) + (4418173 / 12500000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12899 164) (d.w1 12899 164)
      (d.w2 12899 164) ≤
      32 * (((349930413 / 20000000000000000000) : ℝ) + (1244843969 / 100000000000000000000) + (227417151 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12899 164) (d.f1 12899 164) d.f2 ≤
      ((110199571 / 25000000000000000) : ℝ) ^ 2 + 2 * ((110199571 / 25000000000000000)) * ((1470577563 / 1000000000000000000)) * (126 / 100) +
      2 * (((1470577563 / 1000000000000000000)) ^ 2 + 2 * ((110199571 / 25000000000000000)) * ((4418173 / 12500000000000000))) +
      6 * ((1470577563 / 1000000000000000000)) * ((4418173 / 12500000000000000)) * (126 / 100) + 8 * ((4418173 / 12500000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12899 164) (d.f1 12899 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12899 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12899 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12899 164) (d.f1 12899 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12899 164) (d.w1 12899 164) (d.w2 12899 164)
  have hwexpr0 : 0 ≤ d.w0 12899 164 + d.w1 12899 164 * √(π / 2) +
      2 * d.w2 12899 164 + energyR16 12899 *
      radiusPolynomialRoot16 (d.w0 12899 164) (d.w1 12899 164) (d.w2 12899 164) := by
    positivity
  constructor
  · change (12899 : ℝ) ^ 8 * (mA 12899 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12899 164) (d.f1 12899 164) d.f2 + locationR16 12899 *
        radiusPolynomialRoot16 (d.f0 12899 164) (d.f1 12899 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12899 : ℝ) ^ 8 * (mA 12899 : ℝ) ^ 8 *
        ((((110199571 / 25000000000000000) : ℝ) ^ 2 + 2 * ((110199571 / 25000000000000000)) * ((1470577563 / 1000000000000000000)) * (126 / 100) +
          2 * (((1470577563 / 1000000000000000000)) ^ 2 + 2 * ((110199571 / 25000000000000000)) * ((4418173 / 12500000000000000))) +
          6 * ((1470577563 / 1000000000000000000)) * ((4418173 / 12500000000000000)) * (126 / 100) + 8 * ((4418173 / 12500000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12899) *
          (32 * (((110199571 / 25000000000000000) : ℝ) + (1470577563 / 1000000000000000000) + (4418173 / 12500000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12899 : ℝ) ^ 16 *
      (d.w0 12899 164 + d.w1 12899 164 * √(π / 2) + 2 * d.w2 12899 164 +
        energyR16 12899 * radiusPolynomialRoot16 (d.w0 12899 164) (d.w1 12899 164)
          (d.w2 12899 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12899 : ℝ) ^ 16 *
        (((349930413 / 20000000000000000000) : ℝ) + ((1244843969 / 100000000000000000000)) * (126 / 100) + 2 * ((227417151 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12899) *
          (32 * (((349930413 / 20000000000000000000) : ℝ) + (1244843969 / 100000000000000000000) + (227417151 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12899
