import BstLean.Part266Shard18Step4


/-! A coarse bound on the actual paper statistics constant at dimension 12800. -/
namespace BstLean.Part266.Row12800
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12798 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12798 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12798 128 ≤ (13052 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13052 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12800) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12800 : ℕ))
    (by norm_num : (12800 : ℕ) ≤ 16384)
  have ht : paperTail256 12800 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12800 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12800 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12800 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12800 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12800 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12798 128 * √(2 / (12800 : ℝ)) *
      (√(12800 : ℝ) + paperT0 12800 + paperTail256 12800) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12800 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12800 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12800 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12798 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12798 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12800 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12800

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12800
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12800 (61 / 100) 163 (17 / (100 * 12800)) (26 / (10 * 12800)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12800 (61 / 100) 163 (17 / (100 * 12800)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (116366449 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1454580633 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2401656923 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12800 / 12800 * (61 / 100)) ^ 4 * inverseRadius8 (12800 - 1) /
            envelopeGap 12800 (61 / 100) 163 (17 / (100 * 12800)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12800

namespace BstLean.Part266.Row12800
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12800 163 ≤ (4493716253 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12800 163 ≤ (299835929 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (360328343 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12800 163 ≤ (1790566551 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12800 163 ≤ (1273953819 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12800 163 ≤ (465470449 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (116366449 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (116366449 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1454580633 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2401656923 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((455543 / 125000000) : ℝ) ≤ √(17 / (100 * 12800) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12800) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1078732817 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38138964761 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12800) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12800) ≤ (22097087 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12800) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12800 * (163 : ℝ) ^ 2 + 26 / (10 * 12800) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12800) : ℝ)) (tA 12800 * 163 ^ 2 + 26 / (10 * 12800)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((455543 / 125000000))) * ((116366449 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((455543 / 125000000)) ^ 3) * ((1454580633 / 1000000000000000000000000))) + ((2401656923 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((455543 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12800) : ℝ)) d.D d.V d.P (√(tA 12800) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((455543 / 125000000)) ^ 2 * (((1078732817 / 500000000000000)) * ((38138964761 / 1000000000000000000)))) + ((2401656923 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12800) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((455543 / 125000000)) * ((116366449 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12800) : ℝ)) (tA 12800 * 163 ^ 2 + 26 / (10 * 12800)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((116366449 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((455543 / 125000000)) ^ 2) * ((1454580633 / 1000000000000000000000000)) + ((2401656923 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12800) : ℝ)) (√(26 / (10 * 12800) : ℝ)) d.D d.V d.P (√(tA 12800) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((455543 / 125000000)) * (((1078732817 / 500000000000000)) * ((38138964761 / 1000000000000000000))) + ((2401656923 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12800) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((116366449 / 25000000000000000000) : ℝ) + ((2401656923 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12800

namespace BstLean.Part266.Row12800
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12800 163 ∧
    0 ≤ (tableEnvelope C).f1 12800 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12800 163 ∧
    0 ≤ (tableEnvelope C).w1 12800 163 ∧ 0 ≤ (tableEnvelope C).w2 12800 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12800 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12800 163 ∧ 0 ≤ d.f1 12800 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12800 163 ∧ 0 ≤ d.w1 12800 163 ∧ 0 ≤ d.w2 12800 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12800 ≤ 2 * (228 / 100 : ℝ) / 12800 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12800 ≤ 2 * (370 / 100 : ℝ) / 12800 := by
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
    (completeRAData (tableEnvelope C) 12800 163).locationBound 12800 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12800 163).energyBound 12800 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12800 163) (d.f1 12800 163) d.f2 ≤
      32 * (((4493716253 / 1000000000000000000) : ℝ) + (299835929 / 200000000000000000) + (360328343 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12800 163) (d.w1 12800 163)
      (d.w2 12800 163) ≤
      32 * (((1790566551 / 100000000000000000000) : ℝ) + (1273953819 / 100000000000000000000) + (465470449 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12800 163) (d.f1 12800 163) d.f2 ≤
      ((4493716253 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4493716253 / 1000000000000000000)) * ((299835929 / 200000000000000000)) * (126 / 100) +
      2 * (((299835929 / 200000000000000000)) ^ 2 + 2 * ((4493716253 / 1000000000000000000)) * ((360328343 / 1000000000000000000))) +
      6 * ((299835929 / 200000000000000000)) * ((360328343 / 1000000000000000000)) * (126 / 100) + 8 * ((360328343 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12800 163) (d.f1 12800 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12800 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12800 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12800 163) (d.f1 12800 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12800 163) (d.w1 12800 163) (d.w2 12800 163)
  have hwexpr0 : 0 ≤ d.w0 12800 163 + d.w1 12800 163 * √(π / 2) +
      2 * d.w2 12800 163 + energyR16 12800 *
      radiusPolynomialRoot16 (d.w0 12800 163) (d.w1 12800 163) (d.w2 12800 163) := by
    positivity
  constructor
  · change (12800 : ℝ) ^ 8 * (mA 12800 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12800 163) (d.f1 12800 163) d.f2 + locationR16 12800 *
        radiusPolynomialRoot16 (d.f0 12800 163) (d.f1 12800 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12800 : ℝ) ^ 8 * (mA 12800 : ℝ) ^ 8 *
        ((((4493716253 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4493716253 / 1000000000000000000)) * ((299835929 / 200000000000000000)) * (126 / 100) +
          2 * (((299835929 / 200000000000000000)) ^ 2 + 2 * ((4493716253 / 1000000000000000000)) * ((360328343 / 1000000000000000000))) +
          6 * ((299835929 / 200000000000000000)) * ((360328343 / 1000000000000000000)) * (126 / 100) + 8 * ((360328343 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12800) *
          (32 * (((4493716253 / 1000000000000000000) : ℝ) + (299835929 / 200000000000000000) + (360328343 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12800 : ℝ) ^ 16 *
      (d.w0 12800 163 + d.w1 12800 163 * √(π / 2) + 2 * d.w2 12800 163 +
        energyR16 12800 * radiusPolynomialRoot16 (d.w0 12800 163) (d.w1 12800 163)
          (d.w2 12800 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12800 : ℝ) ^ 16 *
        (((1790566551 / 100000000000000000000) : ℝ) + ((1273953819 / 100000000000000000000)) * (126 / 100) + 2 * ((465470449 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12800) *
          (32 * (((1790566551 / 100000000000000000000) : ℝ) + (1273953819 / 100000000000000000000) + (465470449 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12800

/-! A coarse bound on the actual paper statistics constant at dimension 12801. -/
namespace BstLean.Part266.Row12801
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12799 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12799 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12799 128 ≤ (13053 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13053 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12801) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12801 : ℕ))
    (by norm_num : (12801 : ℕ) ≤ 16384)
  have ht : paperTail256 12801 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12801 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12801 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12801 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12801 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12801 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12799 128 * √(2 / (12801 : ℝ)) *
      (√(12801 : ℝ) + paperT0 12801 + paperTail256 12801) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12801 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12801 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12801 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12799 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12799 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12801 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12801

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12801
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12801 (61 / 100) 163 (17 / (100 * 12801)) (26 / (10 * 12801)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12801 (61 / 100) 163 (17 / (100 * 12801)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (232678357 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1454126147 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (240014203 / 50000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12801 / 12801 * (61 / 100)) ^ 4 * inverseRadius8 (12801 - 1) /
            envelopeGap 12801 (61 / 100) 163 (17 / (100 * 12801)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12801

namespace BstLean.Part266.Row12801
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12801 163 ≤ (1123209349 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12801 163 ≤ (1498886571 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (360257937 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12801 163 ≤ (447536669 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12801 163 ≤ (254731029 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12801 163 ≤ (116340341 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (232678357 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (232678357 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1454126147 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (240014203 / 50000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1822101 / 500000000) : ℝ) ≤ √(17 / (100 * 12801) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12801) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1078606409 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19066503003 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12801) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12801) ≤ (27619201 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12801) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12801 * (163 : ℝ) ^ 2 + 26 / (10 * 12801) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12801) : ℝ)) (tA 12801 * 163 ^ 2 + 26 / (10 * 12801)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1822101 / 500000000))) * ((232678357 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1822101 / 500000000)) ^ 3) * ((1454126147 / 1000000000000000000000000))) + ((240014203 / 50000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1822101 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12801) : ℝ)) d.D d.V d.P (√(tA 12801) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1822101 / 500000000)) ^ 2 * (((1078606409 / 500000000000000)) * ((19066503003 / 500000000000000000)))) + ((240014203 / 50000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12801) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1822101 / 500000000)) * ((232678357 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12801) : ℝ)) (tA 12801 * 163 ^ 2 + 26 / (10 * 12801)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((232678357 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1822101 / 500000000)) ^ 2) * ((1454126147 / 1000000000000000000000000)) + ((240014203 / 50000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12801) : ℝ)) (√(26 / (10 * 12801) : ℝ)) d.D d.V d.P (√(tA 12801) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1822101 / 500000000)) * (((1078606409 / 500000000000000)) * ((19066503003 / 500000000000000000))) + ((240014203 / 50000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12801) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((232678357 / 50000000000000000000) : ℝ) + ((240014203 / 50000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12801

namespace BstLean.Part266.Row12801
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12801 163 ∧
    0 ≤ (tableEnvelope C).f1 12801 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12801 163 ∧
    0 ≤ (tableEnvelope C).w1 12801 163 ∧ 0 ≤ (tableEnvelope C).w2 12801 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12801 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12801 163 ∧ 0 ≤ d.f1 12801 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12801 163 ∧ 0 ≤ d.w1 12801 163 ∧ 0 ≤ d.w2 12801 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12801 ≤ 2 * (228 / 100 : ℝ) / 12801 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12801 ≤ 2 * (370 / 100 : ℝ) / 12801 := by
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
    (completeRAData (tableEnvelope C) 12801 163).locationBound 12801 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12801 163).energyBound 12801 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12801 163) (d.f1 12801 163) d.f2 ≤
      32 * (((1123209349 / 250000000000000000) : ℝ) + (1498886571 / 1000000000000000000) + (360257937 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12801 163) (d.w1 12801 163)
      (d.w2 12801 163) ≤
      32 * (((447536669 / 25000000000000000000) : ℝ) + (254731029 / 20000000000000000000) + (116340341 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12801 163) (d.f1 12801 163) d.f2 ≤
      ((1123209349 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1123209349 / 250000000000000000)) * ((1498886571 / 1000000000000000000)) * (126 / 100) +
      2 * (((1498886571 / 1000000000000000000)) ^ 2 + 2 * ((1123209349 / 250000000000000000)) * ((360257937 / 1000000000000000000))) +
      6 * ((1498886571 / 1000000000000000000)) * ((360257937 / 1000000000000000000)) * (126 / 100) + 8 * ((360257937 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12801 163) (d.f1 12801 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12801 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12801 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12801 163) (d.f1 12801 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12801 163) (d.w1 12801 163) (d.w2 12801 163)
  have hwexpr0 : 0 ≤ d.w0 12801 163 + d.w1 12801 163 * √(π / 2) +
      2 * d.w2 12801 163 + energyR16 12801 *
      radiusPolynomialRoot16 (d.w0 12801 163) (d.w1 12801 163) (d.w2 12801 163) := by
    positivity
  constructor
  · change (12801 : ℝ) ^ 8 * (mA 12801 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12801 163) (d.f1 12801 163) d.f2 + locationR16 12801 *
        radiusPolynomialRoot16 (d.f0 12801 163) (d.f1 12801 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12801 : ℝ) ^ 8 * (mA 12801 : ℝ) ^ 8 *
        ((((1123209349 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1123209349 / 250000000000000000)) * ((1498886571 / 1000000000000000000)) * (126 / 100) +
          2 * (((1498886571 / 1000000000000000000)) ^ 2 + 2 * ((1123209349 / 250000000000000000)) * ((360257937 / 1000000000000000000))) +
          6 * ((1498886571 / 1000000000000000000)) * ((360257937 / 1000000000000000000)) * (126 / 100) + 8 * ((360257937 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12801) *
          (32 * (((1123209349 / 250000000000000000) : ℝ) + (1498886571 / 1000000000000000000) + (360257937 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12801 : ℝ) ^ 16 *
      (d.w0 12801 163 + d.w1 12801 163 * √(π / 2) + 2 * d.w2 12801 163 +
        energyR16 12801 * radiusPolynomialRoot16 (d.w0 12801 163) (d.w1 12801 163)
          (d.w2 12801 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12801 : ℝ) ^ 16 *
        (((447536669 / 25000000000000000000) : ℝ) + ((254731029 / 20000000000000000000)) * (126 / 100) + 2 * ((116340341 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12801) *
          (32 * (((447536669 / 25000000000000000000) : ℝ) + (254731029 / 20000000000000000000) + (116340341 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12801

/-! A coarse bound on the actual paper statistics constant at dimension 12802. -/
namespace BstLean.Part266.Row12802
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12800 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12800 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12800 128 ≤ (13054 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13054 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12802) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12802 : ℕ))
    (by norm_num : (12802 : ℕ) ≤ 16384)
  have ht : paperTail256 12802 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12802 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12802 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12802 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12802 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12802 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12800 128 * √(2 / (12802 : ℝ)) *
      (√(12802 : ℝ) + paperT0 12802 + paperTail256 12802) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12802 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12802 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12802 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12800 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12800 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12802 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12802

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12802
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12802 (61 / 100) 163 (17 / (100 * 12802)) (26 / (10 * 12802)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12802 (61 / 100) 163 (17 / (100 * 12802)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (232623833 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (9085449 / 6250000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2398628213 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12802 / 12802 * (61 / 100)) ^ 4 * inverseRadius8 (12802 - 1) /
            envelopeGap 12802 (61 / 100) 163 (17 / (100 * 12802)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12802

namespace BstLean.Part266.Row12802
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12802 163 ≤ (4491958843 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12802 163 ≤ (1498593591 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (11255861 / 31250000000000000)
  w0 : (tableEnvelope C).w0 12802 163 ≤ (894863473 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12802 163 ≤ (1273356571 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12802 163 ≤ (232626157 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (232623833 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (232623833 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (9085449 / 6250000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2398628213 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((182203 / 50000000) : ℝ) ≤ √(17 / (100 * 12802) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12802) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2156960051 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38127048667 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12802) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12802) ≤ (55234087 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12802) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12802 * (163 : ℝ) ^ 2 + 26 / (10 * 12802) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12802) : ℝ)) (tA 12802 * 163 ^ 2 + 26 / (10 * 12802)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((182203 / 50000000))) * ((232623833 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((182203 / 50000000)) ^ 3) * ((9085449 / 6250000000000000000000))) + ((2398628213 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((182203 / 50000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12802) : ℝ)) d.D d.V d.P (√(tA 12802) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((182203 / 50000000)) ^ 2 * (((2156960051 / 1000000000000000)) * ((38127048667 / 1000000000000000000)))) + ((2398628213 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12802) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((182203 / 50000000)) * ((232623833 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12802) : ℝ)) (tA 12802 * 163 ^ 2 + 26 / (10 * 12802)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((232623833 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((182203 / 50000000)) ^ 2) * ((9085449 / 6250000000000000000000)) + ((2398628213 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12802) : ℝ)) (√(26 / (10 * 12802) : ℝ)) d.D d.V d.P (√(tA 12802) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((182203 / 50000000)) * (((2156960051 / 1000000000000000)) * ((38127048667 / 1000000000000000000))) + ((2398628213 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12802) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((232623833 / 50000000000000000000) : ℝ) + ((2398628213 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12802

namespace BstLean.Part266.Row12802
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12802 163 ∧
    0 ≤ (tableEnvelope C).f1 12802 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12802 163 ∧
    0 ≤ (tableEnvelope C).w1 12802 163 ∧ 0 ≤ (tableEnvelope C).w2 12802 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12802 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12802 163 ∧ 0 ≤ d.f1 12802 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12802 163 ∧ 0 ≤ d.w1 12802 163 ∧ 0 ≤ d.w2 12802 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12802 ≤ 2 * (228 / 100 : ℝ) / 12802 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12802 ≤ 2 * (370 / 100 : ℝ) / 12802 := by
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
    (completeRAData (tableEnvelope C) 12802 163).locationBound 12802 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12802 163).energyBound 12802 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12802 163) (d.f1 12802 163) d.f2 ≤
      32 * (((4491958843 / 1000000000000000000) : ℝ) + (1498593591 / 1000000000000000000) + (11255861 / 31250000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12802 163) (d.w1 12802 163)
      (d.w2 12802 163) ≤
      32 * (((894863473 / 50000000000000000000) : ℝ) + (1273356571 / 100000000000000000000) + (232626157 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12802 163) (d.f1 12802 163) d.f2 ≤
      ((4491958843 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4491958843 / 1000000000000000000)) * ((1498593591 / 1000000000000000000)) * (126 / 100) +
      2 * (((1498593591 / 1000000000000000000)) ^ 2 + 2 * ((4491958843 / 1000000000000000000)) * ((11255861 / 31250000000000000))) +
      6 * ((1498593591 / 1000000000000000000)) * ((11255861 / 31250000000000000)) * (126 / 100) + 8 * ((11255861 / 31250000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12802 163) (d.f1 12802 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12802 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12802 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12802 163) (d.f1 12802 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12802 163) (d.w1 12802 163) (d.w2 12802 163)
  have hwexpr0 : 0 ≤ d.w0 12802 163 + d.w1 12802 163 * √(π / 2) +
      2 * d.w2 12802 163 + energyR16 12802 *
      radiusPolynomialRoot16 (d.w0 12802 163) (d.w1 12802 163) (d.w2 12802 163) := by
    positivity
  constructor
  · change (12802 : ℝ) ^ 8 * (mA 12802 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12802 163) (d.f1 12802 163) d.f2 + locationR16 12802 *
        radiusPolynomialRoot16 (d.f0 12802 163) (d.f1 12802 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12802 : ℝ) ^ 8 * (mA 12802 : ℝ) ^ 8 *
        ((((4491958843 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4491958843 / 1000000000000000000)) * ((1498593591 / 1000000000000000000)) * (126 / 100) +
          2 * (((1498593591 / 1000000000000000000)) ^ 2 + 2 * ((4491958843 / 1000000000000000000)) * ((11255861 / 31250000000000000))) +
          6 * ((1498593591 / 1000000000000000000)) * ((11255861 / 31250000000000000)) * (126 / 100) + 8 * ((11255861 / 31250000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12802) *
          (32 * (((4491958843 / 1000000000000000000) : ℝ) + (1498593591 / 1000000000000000000) + (11255861 / 31250000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12802 : ℝ) ^ 16 *
      (d.w0 12802 163 + d.w1 12802 163 * √(π / 2) + 2 * d.w2 12802 163 +
        energyR16 12802 * radiusPolynomialRoot16 (d.w0 12802 163) (d.w1 12802 163)
          (d.w2 12802 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12802 : ℝ) ^ 16 *
        (((894863473 / 50000000000000000000) : ℝ) + ((1273356571 / 100000000000000000000)) * (126 / 100) + 2 * ((232626157 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12802) *
          (32 * (((894863473 / 50000000000000000000) : ℝ) + (1273356571 / 100000000000000000000) + (232626157 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12802

/-! A coarse bound on the actual paper statistics constant at dimension 12803. -/
namespace BstLean.Part266.Row12803
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12801 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12801 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12801 128 ≤ (13055 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13055 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12803) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12803 : ℕ))
    (by norm_num : (12803 : ℕ) ≤ 16384)
  have ht : paperTail256 12803 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12803 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12803 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12803 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12803 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12803 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12801 128 * √(2 / (12803 : ℝ)) *
      (√(12803 : ℝ) + paperT0 12803 + paperTail256 12803) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12803 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12803 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12803 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12801 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12801 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12803 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12803

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12803
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12803 (61 / 100) 163 (17 / (100 * 12803)) (26 / (10 * 12803)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12803 (61 / 100) 163 (17 / (100 * 12803)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (116284663 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1453217709 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4794230943 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12803 / 12803 * (61 / 100)) ^ 4 * inverseRadius8 (12803 - 1) /
            envelopeGap 12803 (61 / 100) 163 (17 / (100 * 12803)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12803

namespace BstLean.Part266.Row12803
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12803 163 ≤ (4491084143 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12803 163 ≤ (1498301527 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (360117287 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12803 163 ≤ (357861617 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12803 163 ≤ (318264611 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12803 163 ≤ (465143297 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (116284663 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (116284663 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1453217709 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4794230943 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3643917 / 1000000000) : ℝ) ≤ √(17 / (100 * 12803) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12803) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2156707333 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7624218541 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12803) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12803) ≤ (55229773 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12803) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12803 * (163 : ℝ) ^ 2 + 26 / (10 * 12803) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12803) : ℝ)) (tA 12803 * 163 ^ 2 + 26 / (10 * 12803)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3643917 / 1000000000))) * ((116284663 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3643917 / 1000000000)) ^ 3) * ((1453217709 / 1000000000000000000000000))) + ((4794230943 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3643917 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12803) : ℝ)) d.D d.V d.P (√(tA 12803) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3643917 / 1000000000)) ^ 2 * (((2156707333 / 1000000000000000)) * ((7624218541 / 200000000000000000)))) + ((4794230943 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12803) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3643917 / 1000000000)) * ((116284663 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12803) : ℝ)) (tA 12803 * 163 ^ 2 + 26 / (10 * 12803)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((116284663 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3643917 / 1000000000)) ^ 2) * ((1453217709 / 1000000000000000000000000)) + ((4794230943 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12803) : ℝ)) (√(26 / (10 * 12803) : ℝ)) d.D d.V d.P (√(tA 12803) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3643917 / 1000000000)) * (((2156707333 / 1000000000000000)) * ((7624218541 / 200000000000000000))) + ((4794230943 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12803) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((116284663 / 25000000000000000000) : ℝ) + ((4794230943 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12803

namespace BstLean.Part266.Row12803
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12803 163 ∧
    0 ≤ (tableEnvelope C).f1 12803 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12803 163 ∧
    0 ≤ (tableEnvelope C).w1 12803 163 ∧ 0 ≤ (tableEnvelope C).w2 12803 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12803 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12803 163 ∧ 0 ≤ d.f1 12803 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12803 163 ∧ 0 ≤ d.w1 12803 163 ∧ 0 ≤ d.w2 12803 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12803 ≤ 2 * (228 / 100 : ℝ) / 12803 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12803 ≤ 2 * (370 / 100 : ℝ) / 12803 := by
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
    (completeRAData (tableEnvelope C) 12803 163).locationBound 12803 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12803 163).energyBound 12803 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12803 163) (d.f1 12803 163) d.f2 ≤
      32 * (((4491084143 / 1000000000000000000) : ℝ) + (1498301527 / 1000000000000000000) + (360117287 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12803 163) (d.w1 12803 163)
      (d.w2 12803 163) ≤
      32 * (((357861617 / 20000000000000000000) : ℝ) + (318264611 / 25000000000000000000) + (465143297 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12803 163) (d.f1 12803 163) d.f2 ≤
      ((4491084143 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4491084143 / 1000000000000000000)) * ((1498301527 / 1000000000000000000)) * (126 / 100) +
      2 * (((1498301527 / 1000000000000000000)) ^ 2 + 2 * ((4491084143 / 1000000000000000000)) * ((360117287 / 1000000000000000000))) +
      6 * ((1498301527 / 1000000000000000000)) * ((360117287 / 1000000000000000000)) * (126 / 100) + 8 * ((360117287 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12803 163) (d.f1 12803 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12803 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12803 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12803 163) (d.f1 12803 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12803 163) (d.w1 12803 163) (d.w2 12803 163)
  have hwexpr0 : 0 ≤ d.w0 12803 163 + d.w1 12803 163 * √(π / 2) +
      2 * d.w2 12803 163 + energyR16 12803 *
      radiusPolynomialRoot16 (d.w0 12803 163) (d.w1 12803 163) (d.w2 12803 163) := by
    positivity
  constructor
  · change (12803 : ℝ) ^ 8 * (mA 12803 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12803 163) (d.f1 12803 163) d.f2 + locationR16 12803 *
        radiusPolynomialRoot16 (d.f0 12803 163) (d.f1 12803 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12803 : ℝ) ^ 8 * (mA 12803 : ℝ) ^ 8 *
        ((((4491084143 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4491084143 / 1000000000000000000)) * ((1498301527 / 1000000000000000000)) * (126 / 100) +
          2 * (((1498301527 / 1000000000000000000)) ^ 2 + 2 * ((4491084143 / 1000000000000000000)) * ((360117287 / 1000000000000000000))) +
          6 * ((1498301527 / 1000000000000000000)) * ((360117287 / 1000000000000000000)) * (126 / 100) + 8 * ((360117287 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12803) *
          (32 * (((4491084143 / 1000000000000000000) : ℝ) + (1498301527 / 1000000000000000000) + (360117287 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12803 : ℝ) ^ 16 *
      (d.w0 12803 163 + d.w1 12803 163 * √(π / 2) + 2 * d.w2 12803 163 +
        energyR16 12803 * radiusPolynomialRoot16 (d.w0 12803 163) (d.w1 12803 163)
          (d.w2 12803 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12803 : ℝ) ^ 16 *
        (((357861617 / 20000000000000000000) : ℝ) + ((318264611 / 25000000000000000000)) * (126 / 100) + 2 * ((465143297 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12803) *
          (32 * (((357861617 / 20000000000000000000) : ℝ) + (318264611 / 25000000000000000000) + (465143297 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12803

/-! A coarse bound on the actual paper statistics constant at dimension 12804. -/
namespace BstLean.Part266.Row12804
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12802 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12802 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12802 128 ≤ (13056 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13056 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12804) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12804 : ℕ))
    (by norm_num : (12804 : ℕ) ≤ 16384)
  have ht : paperTail256 12804 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12804 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12804 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12804 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12804 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12804 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12802 128 * √(2 / (12804 : ℝ)) *
      (√(12804 : ℝ) + paperT0 12804 + paperTail256 12804) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12804 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12804 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12804 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12802 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12802 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12804 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12804

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12804
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12804 (61 / 100) 163 (17 / (100 * 12804)) (26 / (10 * 12804)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12804 (61 / 100) 163 (17 / (100 * 12804)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (58128709 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (363190939 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (598900951 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12804 / 12804 * (61 / 100)) ^ 4 * inverseRadius8 (12804 - 1) /
            envelopeGap 12804 (61 / 100) 163 (17 / (100 * 12804)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12804

namespace BstLean.Part266.Row12804
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12804 163 ≤ (2245103093 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12804 163 ≤ (299601747 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (11251467 / 31250000000000000)
  w0 : (tableEnvelope C).w0 12804 163 ≤ (5590277 / 312500000000000000)
  w1 : (tableEnvelope C).w1 12804 163 ≤ (1272760067 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12804 163 ≤ (232517157 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (58128709 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (58128709 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (363190939 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (598900951 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((145751 / 40000000) : ℝ) ≤ √(17 / (100 * 12804) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12804) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (431290933 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9528784537 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12804) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12804) ≤ (110450919 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12804) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12804 * (163 : ℝ) ^ 2 + 26 / (10 * 12804) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12804) : ℝ)) (tA 12804 * 163 ^ 2 + 26 / (10 * 12804)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((145751 / 40000000))) * ((58128709 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((145751 / 40000000)) ^ 3) * ((363190939 / 250000000000000000000000))) + ((598900951 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((145751 / 40000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12804) : ℝ)) d.D d.V d.P (√(tA 12804) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((145751 / 40000000)) ^ 2 * (((431290933 / 200000000000000)) * ((9528784537 / 250000000000000000)))) + ((598900951 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12804) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((145751 / 40000000)) * ((58128709 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12804) : ℝ)) (tA 12804 * 163 ^ 2 + 26 / (10 * 12804)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((58128709 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((145751 / 40000000)) ^ 2) * ((363190939 / 250000000000000000000000)) + ((598900951 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12804) : ℝ)) (√(26 / (10 * 12804) : ℝ)) d.D d.V d.P (√(tA 12804) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((145751 / 40000000)) * (((431290933 / 200000000000000)) * ((9528784537 / 250000000000000000))) + ((598900951 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12804) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((58128709 / 12500000000000000000) : ℝ) + ((598900951 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12804

namespace BstLean.Part266.Row12804
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12804 163 ∧
    0 ≤ (tableEnvelope C).f1 12804 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12804 163 ∧
    0 ≤ (tableEnvelope C).w1 12804 163 ∧ 0 ≤ (tableEnvelope C).w2 12804 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12804 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12804 163 ∧ 0 ≤ d.f1 12804 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12804 163 ∧ 0 ≤ d.w1 12804 163 ∧ 0 ≤ d.w2 12804 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12804 ≤ 2 * (228 / 100 : ℝ) / 12804 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12804 ≤ 2 * (370 / 100 : ℝ) / 12804 := by
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
    (completeRAData (tableEnvelope C) 12804 163).locationBound 12804 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12804 163).energyBound 12804 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12804 163) (d.f1 12804 163) d.f2 ≤
      32 * (((2245103093 / 500000000000000000) : ℝ) + (299601747 / 200000000000000000) + (11251467 / 31250000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12804 163) (d.w1 12804 163)
      (d.w2 12804 163) ≤
      32 * (((5590277 / 312500000000000000) : ℝ) + (1272760067 / 100000000000000000000) + (232517157 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12804 163) (d.f1 12804 163) d.f2 ≤
      ((2245103093 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2245103093 / 500000000000000000)) * ((299601747 / 200000000000000000)) * (126 / 100) +
      2 * (((299601747 / 200000000000000000)) ^ 2 + 2 * ((2245103093 / 500000000000000000)) * ((11251467 / 31250000000000000))) +
      6 * ((299601747 / 200000000000000000)) * ((11251467 / 31250000000000000)) * (126 / 100) + 8 * ((11251467 / 31250000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12804 163) (d.f1 12804 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12804 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12804 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12804 163) (d.f1 12804 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12804 163) (d.w1 12804 163) (d.w2 12804 163)
  have hwexpr0 : 0 ≤ d.w0 12804 163 + d.w1 12804 163 * √(π / 2) +
      2 * d.w2 12804 163 + energyR16 12804 *
      radiusPolynomialRoot16 (d.w0 12804 163) (d.w1 12804 163) (d.w2 12804 163) := by
    positivity
  constructor
  · change (12804 : ℝ) ^ 8 * (mA 12804 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12804 163) (d.f1 12804 163) d.f2 + locationR16 12804 *
        radiusPolynomialRoot16 (d.f0 12804 163) (d.f1 12804 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12804 : ℝ) ^ 8 * (mA 12804 : ℝ) ^ 8 *
        ((((2245103093 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2245103093 / 500000000000000000)) * ((299601747 / 200000000000000000)) * (126 / 100) +
          2 * (((299601747 / 200000000000000000)) ^ 2 + 2 * ((2245103093 / 500000000000000000)) * ((11251467 / 31250000000000000))) +
          6 * ((299601747 / 200000000000000000)) * ((11251467 / 31250000000000000)) * (126 / 100) + 8 * ((11251467 / 31250000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12804) *
          (32 * (((2245103093 / 500000000000000000) : ℝ) + (299601747 / 200000000000000000) + (11251467 / 31250000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12804 : ℝ) ^ 16 *
      (d.w0 12804 163 + d.w1 12804 163 * √(π / 2) + 2 * d.w2 12804 163 +
        energyR16 12804 * radiusPolynomialRoot16 (d.w0 12804 163) (d.w1 12804 163)
          (d.w2 12804 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12804 : ℝ) ^ 16 *
        (((5590277 / 312500000000000000) : ℝ) + ((1272760067 / 100000000000000000000)) * (126 / 100) + 2 * ((232517157 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12804) *
          (32 * (((5590277 / 312500000000000000) : ℝ) + (1272760067 / 100000000000000000000) + (232517157 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12804

/-! A coarse bound on the actual paper statistics constant at dimension 12805. -/
namespace BstLean.Part266.Row12805
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12803 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12803 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12803 128 ≤ (13057 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13057 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12805) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12805 : ℕ))
    (by norm_num : (12805 : ℕ) ≤ 16384)
  have ht : paperTail256 12805 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12805 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12805 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12805 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12805 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12805 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12803 128 * √(2 / (12805 : ℝ)) *
      (√(12805 : ℝ) + paperT0 12805 + paperTail256 12805) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12805 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12805 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12805 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12803 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12803 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12805 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12805

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12805
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12805 (61 / 100) 163 (17 / (100 * 12805)) (26 / (10 * 12805)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12805 (61 / 100) 163 (17 / (100 * 12805)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (232460363 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (72615499 / 50000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4788186421 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12805 / 12805 * (61 / 100)) ^ 4 * inverseRadius8 (12805 - 1) /
            envelopeGap 12805 (61 / 100) 163 (17 / (100 * 12805)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12805

namespace BstLean.Part266.Row12805
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12805 163 ≤ (280583033 / 62500000000000000)
  f1 : (tableEnvelope C).f1 12805 163 ≤ (374429009 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (359976621 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12805 163 ≤ (894234669 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12805 163 ≤ (127246179 / 10000000000000000000)
  w2 : (tableEnvelope C).w2 12805 163 ≤ (92985073 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (232460363 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (232460363 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (72615499 / 50000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4788186421 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3643633 / 1000000000) : ℝ) ≤ √(17 / (100 * 12805) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12805) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1078101023 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38109184983 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12805) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12805) ≤ (55221147 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12805) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12805 * (163 : ℝ) ^ 2 + 26 / (10 * 12805) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12805) : ℝ)) (tA 12805 * 163 ^ 2 + 26 / (10 * 12805)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3643633 / 1000000000))) * ((232460363 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3643633 / 1000000000)) ^ 3) * ((72615499 / 50000000000000000000000))) + ((4788186421 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3643633 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12805) : ℝ)) d.D d.V d.P (√(tA 12805) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3643633 / 1000000000)) ^ 2 * (((1078101023 / 500000000000000)) * ((38109184983 / 1000000000000000000)))) + ((4788186421 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12805) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3643633 / 1000000000)) * ((232460363 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12805) : ℝ)) (tA 12805 * 163 ^ 2 + 26 / (10 * 12805)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((232460363 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3643633 / 1000000000)) ^ 2) * ((72615499 / 50000000000000000000000)) + ((4788186421 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12805) : ℝ)) (√(26 / (10 * 12805) : ℝ)) d.D d.V d.P (√(tA 12805) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3643633 / 1000000000)) * (((1078101023 / 500000000000000)) * ((38109184983 / 1000000000000000000))) + ((4788186421 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12805) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((232460363 / 50000000000000000000) : ℝ) + ((4788186421 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12805

namespace BstLean.Part266.Row12805
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12805 163 ∧
    0 ≤ (tableEnvelope C).f1 12805 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12805 163 ∧
    0 ≤ (tableEnvelope C).w1 12805 163 ∧ 0 ≤ (tableEnvelope C).w2 12805 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12805 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12805 163 ∧ 0 ≤ d.f1 12805 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12805 163 ∧ 0 ≤ d.w1 12805 163 ∧ 0 ≤ d.w2 12805 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12805 ≤ 2 * (228 / 100 : ℝ) / 12805 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12805 ≤ 2 * (370 / 100 : ℝ) / 12805 := by
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
    (completeRAData (tableEnvelope C) 12805 163).locationBound 12805 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12805 163).energyBound 12805 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12805 163) (d.f1 12805 163) d.f2 ≤
      32 * (((280583033 / 62500000000000000) : ℝ) + (374429009 / 250000000000000000) + (359976621 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12805 163) (d.w1 12805 163)
      (d.w2 12805 163) ≤
      32 * (((894234669 / 50000000000000000000) : ℝ) + (127246179 / 10000000000000000000) + (92985073 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12805 163) (d.f1 12805 163) d.f2 ≤
      ((280583033 / 62500000000000000) : ℝ) ^ 2 + 2 * ((280583033 / 62500000000000000)) * ((374429009 / 250000000000000000)) * (126 / 100) +
      2 * (((374429009 / 250000000000000000)) ^ 2 + 2 * ((280583033 / 62500000000000000)) * ((359976621 / 1000000000000000000))) +
      6 * ((374429009 / 250000000000000000)) * ((359976621 / 1000000000000000000)) * (126 / 100) + 8 * ((359976621 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12805 163) (d.f1 12805 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12805 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12805 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12805 163) (d.f1 12805 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12805 163) (d.w1 12805 163) (d.w2 12805 163)
  have hwexpr0 : 0 ≤ d.w0 12805 163 + d.w1 12805 163 * √(π / 2) +
      2 * d.w2 12805 163 + energyR16 12805 *
      radiusPolynomialRoot16 (d.w0 12805 163) (d.w1 12805 163) (d.w2 12805 163) := by
    positivity
  constructor
  · change (12805 : ℝ) ^ 8 * (mA 12805 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12805 163) (d.f1 12805 163) d.f2 + locationR16 12805 *
        radiusPolynomialRoot16 (d.f0 12805 163) (d.f1 12805 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12805 : ℝ) ^ 8 * (mA 12805 : ℝ) ^ 8 *
        ((((280583033 / 62500000000000000) : ℝ) ^ 2 + 2 * ((280583033 / 62500000000000000)) * ((374429009 / 250000000000000000)) * (126 / 100) +
          2 * (((374429009 / 250000000000000000)) ^ 2 + 2 * ((280583033 / 62500000000000000)) * ((359976621 / 1000000000000000000))) +
          6 * ((374429009 / 250000000000000000)) * ((359976621 / 1000000000000000000)) * (126 / 100) + 8 * ((359976621 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12805) *
          (32 * (((280583033 / 62500000000000000) : ℝ) + (374429009 / 250000000000000000) + (359976621 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12805 : ℝ) ^ 16 *
      (d.w0 12805 163 + d.w1 12805 163 * √(π / 2) + 2 * d.w2 12805 163 +
        energyR16 12805 * radiusPolynomialRoot16 (d.w0 12805 163) (d.w1 12805 163)
          (d.w2 12805 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12805 : ℝ) ^ 16 *
        (((894234669 / 50000000000000000000) : ℝ) + ((127246179 / 10000000000000000000)) * (126 / 100) + 2 * ((92985073 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12805) *
          (32 * (((894234669 / 50000000000000000000) : ℝ) + (127246179 / 10000000000000000000) + (92985073 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12805

/-! A coarse bound on the actual paper statistics constant at dimension 12806. -/
namespace BstLean.Part266.Row12806
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12804 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12804 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12804 128 ≤ (13058 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13058 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12806) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12806 : ℕ))
    (by norm_num : (12806 : ℕ) ≤ 16384)
  have ht : paperTail256 12806 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12806 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12806 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12806 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12806 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12806 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12804 128 * √(2 / (12806 : ℝ)) *
      (√(12806 : ℝ) + paperT0 12806 + paperTail256 12806) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12806 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12806 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12806 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12804 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12804 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12806 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12806

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12806
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12806 (61 / 100) 163 (17 / (100 * 12806)) (26 / (10 * 12806)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12806 (61 / 100) 163 (17 / (100 * 12806)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (232405907 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1451856381 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2392583689 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12806 / 12806 * (61 / 100)) ^ 4 * inverseRadius8 (12806 - 1) /
            envelopeGap 12806 (61 / 100) 163 (17 / (100 * 12806)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12806

namespace BstLean.Part266.Row12806
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12806 163 ≤ (140264099 / 31250000000000000)
  f1 : (tableEnvelope C).f1 12806 163 ≤ (149742343 / 100000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (4498829 / 12500000000000000)
  w0 : (tableEnvelope C).w0 12806 163 ≤ (89402509 / 5000000000000000000)
  w1 : (tableEnvelope C).w1 12806 163 ≤ (1272163611 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12806 163 ≤ (9296329 / 2000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (232405907 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (232405907 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1451856381 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2392583689 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3643491 / 1000000000) : ℝ) ≤ √(17 / (100 * 12806) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12806) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (538987369 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3810323321 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12806) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12806) ≤ (110433669 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12806) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12806 * (163 : ℝ) ^ 2 + 26 / (10 * 12806) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12806) : ℝ)) (tA 12806 * 163 ^ 2 + 26 / (10 * 12806)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3643491 / 1000000000))) * ((232405907 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3643491 / 1000000000)) ^ 3) * ((1451856381 / 1000000000000000000000000))) + ((2392583689 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3643491 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12806) : ℝ)) d.D d.V d.P (√(tA 12806) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3643491 / 1000000000)) ^ 2 * (((538987369 / 250000000000000)) * ((3810323321 / 100000000000000000)))) + ((2392583689 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12806) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3643491 / 1000000000)) * ((232405907 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12806) : ℝ)) (tA 12806 * 163 ^ 2 + 26 / (10 * 12806)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((232405907 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3643491 / 1000000000)) ^ 2) * ((1451856381 / 1000000000000000000000000)) + ((2392583689 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12806) : ℝ)) (√(26 / (10 * 12806) : ℝ)) d.D d.V d.P (√(tA 12806) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3643491 / 1000000000)) * (((538987369 / 250000000000000)) * ((3810323321 / 100000000000000000))) + ((2392583689 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12806) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((232405907 / 50000000000000000000) : ℝ) + ((2392583689 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12806

namespace BstLean.Part266.Row12806
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12806 163 ∧
    0 ≤ (tableEnvelope C).f1 12806 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12806 163 ∧
    0 ≤ (tableEnvelope C).w1 12806 163 ∧ 0 ≤ (tableEnvelope C).w2 12806 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12806 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12806 163 ∧ 0 ≤ d.f1 12806 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12806 163 ∧ 0 ≤ d.w1 12806 163 ∧ 0 ≤ d.w2 12806 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12806 ≤ 2 * (228 / 100 : ℝ) / 12806 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12806 ≤ 2 * (370 / 100 : ℝ) / 12806 := by
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
    (completeRAData (tableEnvelope C) 12806 163).locationBound 12806 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12806 163).energyBound 12806 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12806 163) (d.f1 12806 163) d.f2 ≤
      32 * (((140264099 / 31250000000000000) : ℝ) + (149742343 / 100000000000000000) + (4498829 / 12500000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12806 163) (d.w1 12806 163)
      (d.w2 12806 163) ≤
      32 * (((89402509 / 5000000000000000000) : ℝ) + (1272163611 / 100000000000000000000) + (9296329 / 2000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12806 163) (d.f1 12806 163) d.f2 ≤
      ((140264099 / 31250000000000000) : ℝ) ^ 2 + 2 * ((140264099 / 31250000000000000)) * ((149742343 / 100000000000000000)) * (126 / 100) +
      2 * (((149742343 / 100000000000000000)) ^ 2 + 2 * ((140264099 / 31250000000000000)) * ((4498829 / 12500000000000000))) +
      6 * ((149742343 / 100000000000000000)) * ((4498829 / 12500000000000000)) * (126 / 100) + 8 * ((4498829 / 12500000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12806 163) (d.f1 12806 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12806 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12806 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12806 163) (d.f1 12806 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12806 163) (d.w1 12806 163) (d.w2 12806 163)
  have hwexpr0 : 0 ≤ d.w0 12806 163 + d.w1 12806 163 * √(π / 2) +
      2 * d.w2 12806 163 + energyR16 12806 *
      radiusPolynomialRoot16 (d.w0 12806 163) (d.w1 12806 163) (d.w2 12806 163) := by
    positivity
  constructor
  · change (12806 : ℝ) ^ 8 * (mA 12806 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12806 163) (d.f1 12806 163) d.f2 + locationR16 12806 *
        radiusPolynomialRoot16 (d.f0 12806 163) (d.f1 12806 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12806 : ℝ) ^ 8 * (mA 12806 : ℝ) ^ 8 *
        ((((140264099 / 31250000000000000) : ℝ) ^ 2 + 2 * ((140264099 / 31250000000000000)) * ((149742343 / 100000000000000000)) * (126 / 100) +
          2 * (((149742343 / 100000000000000000)) ^ 2 + 2 * ((140264099 / 31250000000000000)) * ((4498829 / 12500000000000000))) +
          6 * ((149742343 / 100000000000000000)) * ((4498829 / 12500000000000000)) * (126 / 100) + 8 * ((4498829 / 12500000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12806) *
          (32 * (((140264099 / 31250000000000000) : ℝ) + (149742343 / 100000000000000000) + (4498829 / 12500000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12806 : ℝ) ^ 16 *
      (d.w0 12806 163 + d.w1 12806 163 * √(π / 2) + 2 * d.w2 12806 163 +
        energyR16 12806 * radiusPolynomialRoot16 (d.w0 12806 163) (d.w1 12806 163)
          (d.w2 12806 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12806 : ℝ) ^ 16 *
        (((89402509 / 5000000000000000000) : ℝ) + ((1272163611 / 100000000000000000000)) * (126 / 100) + 2 * ((9296329 / 2000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12806) *
          (32 * (((89402509 / 5000000000000000000) : ℝ) + (1272163611 / 100000000000000000000) + (9296329 / 2000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12806

/-! A coarse bound on the actual paper statistics constant at dimension 12807. -/
namespace BstLean.Part266.Row12807
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12805 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12805 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12805 128 ≤ (13059 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13059 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12807) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12807 : ℕ))
    (by norm_num : (12807 : ℕ) ≤ 16384)
  have ht : paperTail256 12807 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12807 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12807 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12807 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12807 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12807 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12805 128 * √(2 / (12807 : ℝ)) *
      (√(12807 : ℝ) + paperT0 12807 + paperTail256 12807) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12807 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12807 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12807 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12805 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12805 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12807 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12807

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12807
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12807 (61 / 100) 163 (17 / (100 * 12807)) (26 / (10 * 12807)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12807 (61 / 100) 163 (17 / (100 * 12807)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (58087867 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1451402959 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4782150479 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12807 / 12807 * (61 / 100)) ^ 4 * inverseRadius8 (12807 - 1) /
            envelopeGap 12807 (61 / 100) 163 (17 / (100 * 12807)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12807

namespace BstLean.Part266.Row12807
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12807 163 ≤ (4487577663 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12807 163 ≤ (74856587 / 50000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (179918069 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12807 163 ≤ (178763189 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 12807 163 ≤ (31796647 / 2500000000000000000)
  w2 : (tableEnvelope C).w2 12807 163 ≤ (464707569 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (58087867 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (58087867 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1451402959 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4782150479 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((910837 / 250000000) : ℝ) ≤ √(17 / (100 * 12807) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12807) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (431139391 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3809728283 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12807) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12807) ≤ (55212523 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12807) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12807 * (163 : ℝ) ^ 2 + 26 / (10 * 12807) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12807) : ℝ)) (tA 12807 * 163 ^ 2 + 26 / (10 * 12807)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((910837 / 250000000))) * ((58087867 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((910837 / 250000000)) ^ 3) * ((1451402959 / 1000000000000000000000000))) + ((4782150479 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((910837 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12807) : ℝ)) d.D d.V d.P (√(tA 12807) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((910837 / 250000000)) ^ 2 * (((431139391 / 200000000000000)) * ((3809728283 / 100000000000000000)))) + ((4782150479 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12807) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((910837 / 250000000)) * ((58087867 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12807) : ℝ)) (tA 12807 * 163 ^ 2 + 26 / (10 * 12807)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((58087867 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((910837 / 250000000)) ^ 2) * ((1451402959 / 1000000000000000000000000)) + ((4782150479 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12807) : ℝ)) (√(26 / (10 * 12807) : ℝ)) d.D d.V d.P (√(tA 12807) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((910837 / 250000000)) * (((431139391 / 200000000000000)) * ((3809728283 / 100000000000000000))) + ((4782150479 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12807) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((58087867 / 12500000000000000000) : ℝ) + ((4782150479 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12807

namespace BstLean.Part266.Row12807
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12807 163 ∧
    0 ≤ (tableEnvelope C).f1 12807 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12807 163 ∧
    0 ≤ (tableEnvelope C).w1 12807 163 ∧ 0 ≤ (tableEnvelope C).w2 12807 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12807 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12807 163 ∧ 0 ≤ d.f1 12807 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12807 163 ∧ 0 ≤ d.w1 12807 163 ∧ 0 ≤ d.w2 12807 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12807 ≤ 2 * (228 / 100 : ℝ) / 12807 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12807 ≤ 2 * (370 / 100 : ℝ) / 12807 := by
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
    (completeRAData (tableEnvelope C) 12807 163).locationBound 12807 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12807 163).energyBound 12807 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12807 163) (d.f1 12807 163) d.f2 ≤
      32 * (((4487577663 / 1000000000000000000) : ℝ) + (74856587 / 50000000000000000) + (179918069 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12807 163) (d.w1 12807 163)
      (d.w2 12807 163) ≤
      32 * (((178763189 / 10000000000000000000) : ℝ) + (31796647 / 2500000000000000000) + (464707569 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12807 163) (d.f1 12807 163) d.f2 ≤
      ((4487577663 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4487577663 / 1000000000000000000)) * ((74856587 / 50000000000000000)) * (126 / 100) +
      2 * (((74856587 / 50000000000000000)) ^ 2 + 2 * ((4487577663 / 1000000000000000000)) * ((179918069 / 500000000000000000))) +
      6 * ((74856587 / 50000000000000000)) * ((179918069 / 500000000000000000)) * (126 / 100) + 8 * ((179918069 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12807 163) (d.f1 12807 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12807 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12807 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12807 163) (d.f1 12807 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12807 163) (d.w1 12807 163) (d.w2 12807 163)
  have hwexpr0 : 0 ≤ d.w0 12807 163 + d.w1 12807 163 * √(π / 2) +
      2 * d.w2 12807 163 + energyR16 12807 *
      radiusPolynomialRoot16 (d.w0 12807 163) (d.w1 12807 163) (d.w2 12807 163) := by
    positivity
  constructor
  · change (12807 : ℝ) ^ 8 * (mA 12807 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12807 163) (d.f1 12807 163) d.f2 + locationR16 12807 *
        radiusPolynomialRoot16 (d.f0 12807 163) (d.f1 12807 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12807 : ℝ) ^ 8 * (mA 12807 : ℝ) ^ 8 *
        ((((4487577663 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4487577663 / 1000000000000000000)) * ((74856587 / 50000000000000000)) * (126 / 100) +
          2 * (((74856587 / 50000000000000000)) ^ 2 + 2 * ((4487577663 / 1000000000000000000)) * ((179918069 / 500000000000000000))) +
          6 * ((74856587 / 50000000000000000)) * ((179918069 / 500000000000000000)) * (126 / 100) + 8 * ((179918069 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12807) *
          (32 * (((4487577663 / 1000000000000000000) : ℝ) + (74856587 / 50000000000000000) + (179918069 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12807 : ℝ) ^ 16 *
      (d.w0 12807 163 + d.w1 12807 163 * √(π / 2) + 2 * d.w2 12807 163 +
        energyR16 12807 * radiusPolynomialRoot16 (d.w0 12807 163) (d.w1 12807 163)
          (d.w2 12807 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12807 : ℝ) ^ 16 *
        (((178763189 / 10000000000000000000) : ℝ) + ((31796647 / 2500000000000000000)) * (126 / 100) + 2 * ((464707569 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12807) *
          (32 * (((178763189 / 10000000000000000000) : ℝ) + (31796647 / 2500000000000000000) + (464707569 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12807

/-! A coarse bound on the actual paper statistics constant at dimension 12808. -/
namespace BstLean.Part266.Row12808
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12806 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12806 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12806 128 ≤ (13060 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13060 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12808) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12808 : ℕ))
    (by norm_num : (12808 : ℕ) ≤ 16384)
  have ht : paperTail256 12808 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12808 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12808 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12808 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12808 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12808 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12806 128 * √(2 / (12808 : ℝ)) *
      (√(12808 : ℝ) + paperT0 12808 + paperTail256 12808) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12808 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12808 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12808 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12806 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12806 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12808 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12808

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12808
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12808 (61 / 100) 163 (17 / (100 * 12808)) (26 / (10 * 12808)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12808 (61 / 100) 163 (17 / (100 * 12808)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (116148523 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (290189943 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2389567861 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12808 / 12808 * (61 / 100)) ^ 4 * inverseRadius8 (12808 - 1) /
            envelopeGap 12808 (61 / 100) 163 (17 / (100 * 12808)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12808

namespace BstLean.Part266.Row12808
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12808 163 ≤ (560837613 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12808 163 ≤ (1496839323 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (179882939 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12808 163 ≤ (893606509 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12808 163 ≤ (1271567899 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12808 163 ≤ (232299361 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (116148523 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (116148523 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (290189943 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2389567861 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1821603 / 500000000) : ℝ) ≤ √(17 / (100 * 12808) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12808) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (538861121 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38091333857 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12808) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12808) ≤ (4416657 / 40000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12808) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12808 * (163 : ℝ) ^ 2 + 26 / (10 * 12808) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12808) : ℝ)) (tA 12808 * 163 ^ 2 + 26 / (10 * 12808)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1821603 / 500000000))) * ((116148523 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1821603 / 500000000)) ^ 3) * ((290189943 / 200000000000000000000000))) + ((2389567861 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1821603 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12808) : ℝ)) d.D d.V d.P (√(tA 12808) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1821603 / 500000000)) ^ 2 * (((538861121 / 250000000000000)) * ((38091333857 / 1000000000000000000)))) + ((2389567861 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12808) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1821603 / 500000000)) * ((116148523 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12808) : ℝ)) (tA 12808 * 163 ^ 2 + 26 / (10 * 12808)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((116148523 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1821603 / 500000000)) ^ 2) * ((290189943 / 200000000000000000000000)) + ((2389567861 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12808) : ℝ)) (√(26 / (10 * 12808) : ℝ)) d.D d.V d.P (√(tA 12808) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1821603 / 500000000)) * (((538861121 / 250000000000000)) * ((38091333857 / 1000000000000000000))) + ((2389567861 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12808) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((116148523 / 25000000000000000000) : ℝ) + ((2389567861 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12808

namespace BstLean.Part266.Row12808
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12808 163 ∧
    0 ≤ (tableEnvelope C).f1 12808 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12808 163 ∧
    0 ≤ (tableEnvelope C).w1 12808 163 ∧ 0 ≤ (tableEnvelope C).w2 12808 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12808 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12808 163 ∧ 0 ≤ d.f1 12808 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12808 163 ∧ 0 ≤ d.w1 12808 163 ∧ 0 ≤ d.w2 12808 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12808 ≤ 2 * (228 / 100 : ℝ) / 12808 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12808 ≤ 2 * (370 / 100 : ℝ) / 12808 := by
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
    (completeRAData (tableEnvelope C) 12808 163).locationBound 12808 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12808 163).energyBound 12808 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12808 163) (d.f1 12808 163) d.f2 ≤
      32 * (((560837613 / 125000000000000000) : ℝ) + (1496839323 / 1000000000000000000) + (179882939 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12808 163) (d.w1 12808 163)
      (d.w2 12808 163) ≤
      32 * (((893606509 / 50000000000000000000) : ℝ) + (1271567899 / 100000000000000000000) + (232299361 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12808 163) (d.f1 12808 163) d.f2 ≤
      ((560837613 / 125000000000000000) : ℝ) ^ 2 + 2 * ((560837613 / 125000000000000000)) * ((1496839323 / 1000000000000000000)) * (126 / 100) +
      2 * (((1496839323 / 1000000000000000000)) ^ 2 + 2 * ((560837613 / 125000000000000000)) * ((179882939 / 500000000000000000))) +
      6 * ((1496839323 / 1000000000000000000)) * ((179882939 / 500000000000000000)) * (126 / 100) + 8 * ((179882939 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12808 163) (d.f1 12808 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12808 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12808 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12808 163) (d.f1 12808 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12808 163) (d.w1 12808 163) (d.w2 12808 163)
  have hwexpr0 : 0 ≤ d.w0 12808 163 + d.w1 12808 163 * √(π / 2) +
      2 * d.w2 12808 163 + energyR16 12808 *
      radiusPolynomialRoot16 (d.w0 12808 163) (d.w1 12808 163) (d.w2 12808 163) := by
    positivity
  constructor
  · change (12808 : ℝ) ^ 8 * (mA 12808 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12808 163) (d.f1 12808 163) d.f2 + locationR16 12808 *
        radiusPolynomialRoot16 (d.f0 12808 163) (d.f1 12808 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12808 : ℝ) ^ 8 * (mA 12808 : ℝ) ^ 8 *
        ((((560837613 / 125000000000000000) : ℝ) ^ 2 + 2 * ((560837613 / 125000000000000000)) * ((1496839323 / 1000000000000000000)) * (126 / 100) +
          2 * (((1496839323 / 1000000000000000000)) ^ 2 + 2 * ((560837613 / 125000000000000000)) * ((179882939 / 500000000000000000))) +
          6 * ((1496839323 / 1000000000000000000)) * ((179882939 / 500000000000000000)) * (126 / 100) + 8 * ((179882939 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12808) *
          (32 * (((560837613 / 125000000000000000) : ℝ) + (1496839323 / 1000000000000000000) + (179882939 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12808 : ℝ) ^ 16 *
      (d.w0 12808 163 + d.w1 12808 163 * √(π / 2) + 2 * d.w2 12808 163 +
        energyR16 12808 * radiusPolynomialRoot16 (d.w0 12808 163) (d.w1 12808 163)
          (d.w2 12808 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12808 : ℝ) ^ 16 *
        (((893606509 / 50000000000000000000) : ℝ) + ((1271567899 / 100000000000000000000)) * (126 / 100) + 2 * ((232299361 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12808) *
          (32 * (((893606509 / 50000000000000000000) : ℝ) + (1271567899 / 100000000000000000000) + (232299361 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12808

/-! A coarse bound on the actual paper statistics constant at dimension 12809. -/
namespace BstLean.Part266.Row12809
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12807 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12807 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12807 128 ≤ (13061 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13061 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12809) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12809 : ℕ))
    (by norm_num : (12809 : ℕ) ≤ 16384)
  have ht : paperTail256 12809 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12809 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12809 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12809 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12809 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12809 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12807 128 * √(2 / (12809 : ℝ)) *
      (√(12809 : ℝ) + paperT0 12809 + paperTail256 12809) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12809 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12809 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12809 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12807 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12807 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12809 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12809

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12809
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12809 (61 / 100) 163 (17 / (100 * 12809)) (26 / (10 * 12809)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12809 (61 / 100) 163 (17 / (100 * 12809)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (232242641 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1450496647 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (955224621 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12809 / 12809 * (61 / 100)) ^ 4 * inverseRadius8 (12809 - 1) /
            envelopeGap 12809 (61 / 100) 163 (17 / (100 * 12809)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12809

namespace BstLean.Part266.Row12809
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12809 163 ≤ (112145611 / 25000000000000000)
  f1 : (tableEnvelope C).f1 12809 163 ≤ (748273499 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (359695639 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12809 163 ≤ (111674643 / 6250000000000000000)
  w1 : (tableEnvelope C).w1 12809 163 ≤ (1271270017 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12809 163 ≤ (464489909 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (232242641 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (232242641 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1450496647 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (955224621 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((455383 / 125000000) : ℝ) ≤ √(17 / (100 * 12809) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12809) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1077596031 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19042693133 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12809) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12809) ≤ (22081561 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12809) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12809 * (163 : ℝ) ^ 2 + 26 / (10 * 12809) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12809) : ℝ)) (tA 12809 * 163 ^ 2 + 26 / (10 * 12809)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((455383 / 125000000))) * ((232242641 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((455383 / 125000000)) ^ 3) * ((1450496647 / 1000000000000000000000000))) + ((955224621 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((455383 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12809) : ℝ)) d.D d.V d.P (√(tA 12809) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((455383 / 125000000)) ^ 2 * (((1077596031 / 500000000000000)) * ((19042693133 / 500000000000000000)))) + ((955224621 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12809) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((455383 / 125000000)) * ((232242641 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12809) : ℝ)) (tA 12809 * 163 ^ 2 + 26 / (10 * 12809)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((232242641 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((455383 / 125000000)) ^ 2) * ((1450496647 / 1000000000000000000000000)) + ((955224621 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12809) : ℝ)) (√(26 / (10 * 12809) : ℝ)) d.D d.V d.P (√(tA 12809) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((455383 / 125000000)) * (((1077596031 / 500000000000000)) * ((19042693133 / 500000000000000000))) + ((955224621 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12809) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((232242641 / 50000000000000000000) : ℝ) + ((955224621 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12809

namespace BstLean.Part266.Row12809
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12809 163 ∧
    0 ≤ (tableEnvelope C).f1 12809 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12809 163 ∧
    0 ≤ (tableEnvelope C).w1 12809 163 ∧ 0 ≤ (tableEnvelope C).w2 12809 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12809 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12809 163 ∧ 0 ≤ d.f1 12809 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12809 163 ∧ 0 ≤ d.w1 12809 163 ∧ 0 ≤ d.w2 12809 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12809 ≤ 2 * (228 / 100 : ℝ) / 12809 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12809 ≤ 2 * (370 / 100 : ℝ) / 12809 := by
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
    (completeRAData (tableEnvelope C) 12809 163).locationBound 12809 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12809 163).energyBound 12809 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12809 163) (d.f1 12809 163) d.f2 ≤
      32 * (((112145611 / 25000000000000000) : ℝ) + (748273499 / 500000000000000000) + (359695639 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12809 163) (d.w1 12809 163)
      (d.w2 12809 163) ≤
      32 * (((111674643 / 6250000000000000000) : ℝ) + (1271270017 / 100000000000000000000) + (464489909 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12809 163) (d.f1 12809 163) d.f2 ≤
      ((112145611 / 25000000000000000) : ℝ) ^ 2 + 2 * ((112145611 / 25000000000000000)) * ((748273499 / 500000000000000000)) * (126 / 100) +
      2 * (((748273499 / 500000000000000000)) ^ 2 + 2 * ((112145611 / 25000000000000000)) * ((359695639 / 1000000000000000000))) +
      6 * ((748273499 / 500000000000000000)) * ((359695639 / 1000000000000000000)) * (126 / 100) + 8 * ((359695639 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12809 163) (d.f1 12809 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12809 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12809 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12809 163) (d.f1 12809 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12809 163) (d.w1 12809 163) (d.w2 12809 163)
  have hwexpr0 : 0 ≤ d.w0 12809 163 + d.w1 12809 163 * √(π / 2) +
      2 * d.w2 12809 163 + energyR16 12809 *
      radiusPolynomialRoot16 (d.w0 12809 163) (d.w1 12809 163) (d.w2 12809 163) := by
    positivity
  constructor
  · change (12809 : ℝ) ^ 8 * (mA 12809 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12809 163) (d.f1 12809 163) d.f2 + locationR16 12809 *
        radiusPolynomialRoot16 (d.f0 12809 163) (d.f1 12809 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12809 : ℝ) ^ 8 * (mA 12809 : ℝ) ^ 8 *
        ((((112145611 / 25000000000000000) : ℝ) ^ 2 + 2 * ((112145611 / 25000000000000000)) * ((748273499 / 500000000000000000)) * (126 / 100) +
          2 * (((748273499 / 500000000000000000)) ^ 2 + 2 * ((112145611 / 25000000000000000)) * ((359695639 / 1000000000000000000))) +
          6 * ((748273499 / 500000000000000000)) * ((359695639 / 1000000000000000000)) * (126 / 100) + 8 * ((359695639 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12809) *
          (32 * (((112145611 / 25000000000000000) : ℝ) + (748273499 / 500000000000000000) + (359695639 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12809 : ℝ) ^ 16 *
      (d.w0 12809 163 + d.w1 12809 163 * √(π / 2) + 2 * d.w2 12809 163 +
        energyR16 12809 * radiusPolynomialRoot16 (d.w0 12809 163) (d.w1 12809 163)
          (d.w2 12809 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12809 : ℝ) ^ 16 *
        (((111674643 / 6250000000000000000) : ℝ) + ((1271270017 / 100000000000000000000)) * (126 / 100) + 2 * ((464489909 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12809) *
          (32 * (((111674643 / 6250000000000000000) : ℝ) + (1271270017 / 100000000000000000000) + (464489909 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12809

/-! A coarse bound on the actual paper statistics constant at dimension 12810. -/
namespace BstLean.Part266.Row12810
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12808 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12808 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12808 128 ≤ (13062 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13062 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12810) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12810 : ℕ))
    (by norm_num : (12810 : ℕ) ≤ 16384)
  have ht : paperTail256 12810 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12810 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12810 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12810 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12810 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12810 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12808 128 * √(2 / (12810 : ℝ)) *
      (√(12810 : ℝ) + paperT0 12810 + paperTail256 12810) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12810 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12810 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12810 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12808 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12808 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12810 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12810

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12810
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12810 (61 / 100) 163 (17 / (100 * 12810)) (26 / (10 * 12810)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12810 (61 / 100) 163 (17 / (100 * 12810)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (232188253 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (362510939 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2386556313 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12810 / 12810 * (61 / 100)) ^ 4 * inverseRadius8 (12810 - 1) /
            envelopeGap 12810 (61 / 100) 163 (17 / (100 * 12810)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12810

namespace BstLean.Part266.Row12810
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12810 163 ≤ (1121237069 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12810 163 ≤ (1496254767 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (359625421 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12810 163 ≤ (1786375701 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12810 163 ≤ (1270972233 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12810 163 ≤ (46438113 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (232188253 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (232188253 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (362510939 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2386556313 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1821461 / 500000000) : ℝ) ≤ √(17 / (100 * 12810) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12810) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2154939689 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3807944007 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12810) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12810) ≤ (55199593 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12810) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12810 * (163 : ℝ) ^ 2 + 26 / (10 * 12810) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12810) : ℝ)) (tA 12810 * 163 ^ 2 + 26 / (10 * 12810)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1821461 / 500000000))) * ((232188253 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1821461 / 500000000)) ^ 3) * ((362510939 / 250000000000000000000000))) + ((2386556313 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1821461 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12810) : ℝ)) d.D d.V d.P (√(tA 12810) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1821461 / 500000000)) ^ 2 * (((2154939689 / 1000000000000000)) * ((3807944007 / 100000000000000000)))) + ((2386556313 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12810) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1821461 / 500000000)) * ((232188253 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12810) : ℝ)) (tA 12810 * 163 ^ 2 + 26 / (10 * 12810)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((232188253 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1821461 / 500000000)) ^ 2) * ((362510939 / 250000000000000000000000)) + ((2386556313 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12810) : ℝ)) (√(26 / (10 * 12810) : ℝ)) d.D d.V d.P (√(tA 12810) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1821461 / 500000000)) * (((2154939689 / 1000000000000000)) * ((3807944007 / 100000000000000000))) + ((2386556313 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12810) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((232188253 / 50000000000000000000) : ℝ) + ((2386556313 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12810

namespace BstLean.Part266.Row12810
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12810 163 ∧
    0 ≤ (tableEnvelope C).f1 12810 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12810 163 ∧
    0 ≤ (tableEnvelope C).w1 12810 163 ∧ 0 ≤ (tableEnvelope C).w2 12810 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12810 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12810 163 ∧ 0 ≤ d.f1 12810 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12810 163 ∧ 0 ≤ d.w1 12810 163 ∧ 0 ≤ d.w2 12810 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12810 ≤ 2 * (228 / 100 : ℝ) / 12810 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12810 ≤ 2 * (370 / 100 : ℝ) / 12810 := by
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
    (completeRAData (tableEnvelope C) 12810 163).locationBound 12810 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12810 163).energyBound 12810 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12810 163) (d.f1 12810 163) d.f2 ≤
      32 * (((1121237069 / 250000000000000000) : ℝ) + (1496254767 / 1000000000000000000) + (359625421 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12810 163) (d.w1 12810 163)
      (d.w2 12810 163) ≤
      32 * (((1786375701 / 100000000000000000000) : ℝ) + (1270972233 / 100000000000000000000) + (46438113 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12810 163) (d.f1 12810 163) d.f2 ≤
      ((1121237069 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1121237069 / 250000000000000000)) * ((1496254767 / 1000000000000000000)) * (126 / 100) +
      2 * (((1496254767 / 1000000000000000000)) ^ 2 + 2 * ((1121237069 / 250000000000000000)) * ((359625421 / 1000000000000000000))) +
      6 * ((1496254767 / 1000000000000000000)) * ((359625421 / 1000000000000000000)) * (126 / 100) + 8 * ((359625421 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12810 163) (d.f1 12810 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12810 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12810 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12810 163) (d.f1 12810 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12810 163) (d.w1 12810 163) (d.w2 12810 163)
  have hwexpr0 : 0 ≤ d.w0 12810 163 + d.w1 12810 163 * √(π / 2) +
      2 * d.w2 12810 163 + energyR16 12810 *
      radiusPolynomialRoot16 (d.w0 12810 163) (d.w1 12810 163) (d.w2 12810 163) := by
    positivity
  constructor
  · change (12810 : ℝ) ^ 8 * (mA 12810 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12810 163) (d.f1 12810 163) d.f2 + locationR16 12810 *
        radiusPolynomialRoot16 (d.f0 12810 163) (d.f1 12810 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12810 : ℝ) ^ 8 * (mA 12810 : ℝ) ^ 8 *
        ((((1121237069 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1121237069 / 250000000000000000)) * ((1496254767 / 1000000000000000000)) * (126 / 100) +
          2 * (((1496254767 / 1000000000000000000)) ^ 2 + 2 * ((1121237069 / 250000000000000000)) * ((359625421 / 1000000000000000000))) +
          6 * ((1496254767 / 1000000000000000000)) * ((359625421 / 1000000000000000000)) * (126 / 100) + 8 * ((359625421 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12810) *
          (32 * (((1121237069 / 250000000000000000) : ℝ) + (1496254767 / 1000000000000000000) + (359625421 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12810 : ℝ) ^ 16 *
      (d.w0 12810 163 + d.w1 12810 163 * √(π / 2) + 2 * d.w2 12810 163 +
        energyR16 12810 * radiusPolynomialRoot16 (d.w0 12810 163) (d.w1 12810 163)
          (d.w2 12810 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12810 : ℝ) ^ 16 *
        (((1786375701 / 100000000000000000000) : ℝ) + ((1270972233 / 100000000000000000000)) * (126 / 100) + 2 * ((46438113 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12810) *
          (32 * (((1786375701 / 100000000000000000000) : ℝ) + (1270972233 / 100000000000000000000) + (46438113 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12810

/-! A coarse bound on the actual paper statistics constant at dimension 12811. -/
namespace BstLean.Part266.Row12811
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12809 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12809 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12809 128 ≤ (13063 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13063 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12811) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12811 : ℕ))
    (by norm_num : (12811 : ℕ) ≤ 16384)
  have ht : paperTail256 12811 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12811 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12811 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12811 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12811 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12811 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12809 128 * √(2 / (12811 : ℝ)) *
      (√(12811 : ℝ) + paperT0 12811 + paperTail256 12811) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12811 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12811 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12811 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12809 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12809 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12811 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12811

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12811
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12811 (61 / 100) 163 (17 / (100 * 12811)) (26 / (10 * 12811)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12811 (61 / 100) 163 (17 / (100 * 12811)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (116066941 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1449591041 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1192526071 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12811 / 12811 * (61 / 100)) ^ 4 * inverseRadius8 (12811 - 1) /
            envelopeGap 12811 (61 / 100) 163 (17 / (100 * 12811)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12811

namespace BstLean.Part266.Row12811
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12811 163 ≤ (4484072409 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12811 163 ≤ (1495962629 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (359555223 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12811 163 ≤ (223244657 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 12811 163 ≤ (317668637 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12811 163 ≤ (92854477 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (116066941 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (116066941 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1449591041 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1192526071 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((182139 / 50000000) : ℝ) ≤ √(17 / (100 * 12811) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12811) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (430937473 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4759186907 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12811) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12811) ≤ (13798821 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12811) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12811 * (163 : ℝ) ^ 2 + 26 / (10 * 12811) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12811) : ℝ)) (tA 12811 * 163 ^ 2 + 26 / (10 * 12811)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((182139 / 50000000))) * ((116066941 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((182139 / 50000000)) ^ 3) * ((1449591041 / 1000000000000000000000000))) + ((1192526071 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((182139 / 50000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12811) : ℝ)) d.D d.V d.P (√(tA 12811) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((182139 / 50000000)) ^ 2 * (((430937473 / 200000000000000)) * ((4759186907 / 125000000000000000)))) + ((1192526071 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12811) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((182139 / 50000000)) * ((116066941 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12811) : ℝ)) (tA 12811 * 163 ^ 2 + 26 / (10 * 12811)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((116066941 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((182139 / 50000000)) ^ 2) * ((1449591041 / 1000000000000000000000000)) + ((1192526071 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12811) : ℝ)) (√(26 / (10 * 12811) : ℝ)) d.D d.V d.P (√(tA 12811) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((182139 / 50000000)) * (((430937473 / 200000000000000)) * ((4759186907 / 125000000000000000))) + ((1192526071 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12811) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((116066941 / 25000000000000000000) : ℝ) + ((1192526071 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12811

namespace BstLean.Part266.Row12811
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12811 163 ∧
    0 ≤ (tableEnvelope C).f1 12811 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12811 163 ∧
    0 ≤ (tableEnvelope C).w1 12811 163 ∧ 0 ≤ (tableEnvelope C).w2 12811 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12811 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12811 163 ∧ 0 ≤ d.f1 12811 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12811 163 ∧ 0 ≤ d.w1 12811 163 ∧ 0 ≤ d.w2 12811 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12811 ≤ 2 * (228 / 100 : ℝ) / 12811 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12811 ≤ 2 * (370 / 100 : ℝ) / 12811 := by
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
    (completeRAData (tableEnvelope C) 12811 163).locationBound 12811 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12811 163).energyBound 12811 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12811 163) (d.f1 12811 163) d.f2 ≤
      32 * (((4484072409 / 1000000000000000000) : ℝ) + (1495962629 / 1000000000000000000) + (359555223 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12811 163) (d.w1 12811 163)
      (d.w2 12811 163) ≤
      32 * (((223244657 / 12500000000000000000) : ℝ) + (317668637 / 25000000000000000000) + (92854477 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12811 163) (d.f1 12811 163) d.f2 ≤
      ((4484072409 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4484072409 / 1000000000000000000)) * ((1495962629 / 1000000000000000000)) * (126 / 100) +
      2 * (((1495962629 / 1000000000000000000)) ^ 2 + 2 * ((4484072409 / 1000000000000000000)) * ((359555223 / 1000000000000000000))) +
      6 * ((1495962629 / 1000000000000000000)) * ((359555223 / 1000000000000000000)) * (126 / 100) + 8 * ((359555223 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12811 163) (d.f1 12811 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12811 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12811 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12811 163) (d.f1 12811 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12811 163) (d.w1 12811 163) (d.w2 12811 163)
  have hwexpr0 : 0 ≤ d.w0 12811 163 + d.w1 12811 163 * √(π / 2) +
      2 * d.w2 12811 163 + energyR16 12811 *
      radiusPolynomialRoot16 (d.w0 12811 163) (d.w1 12811 163) (d.w2 12811 163) := by
    positivity
  constructor
  · change (12811 : ℝ) ^ 8 * (mA 12811 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12811 163) (d.f1 12811 163) d.f2 + locationR16 12811 *
        radiusPolynomialRoot16 (d.f0 12811 163) (d.f1 12811 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12811 : ℝ) ^ 8 * (mA 12811 : ℝ) ^ 8 *
        ((((4484072409 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4484072409 / 1000000000000000000)) * ((1495962629 / 1000000000000000000)) * (126 / 100) +
          2 * (((1495962629 / 1000000000000000000)) ^ 2 + 2 * ((4484072409 / 1000000000000000000)) * ((359555223 / 1000000000000000000))) +
          6 * ((1495962629 / 1000000000000000000)) * ((359555223 / 1000000000000000000)) * (126 / 100) + 8 * ((359555223 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12811) *
          (32 * (((4484072409 / 1000000000000000000) : ℝ) + (1495962629 / 1000000000000000000) + (359555223 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12811 : ℝ) ^ 16 *
      (d.w0 12811 163 + d.w1 12811 163 * √(π / 2) + 2 * d.w2 12811 163 +
        energyR16 12811 * radiusPolynomialRoot16 (d.w0 12811 163) (d.w1 12811 163)
          (d.w2 12811 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12811 : ℝ) ^ 16 *
        (((223244657 / 12500000000000000000) : ℝ) + ((317668637 / 25000000000000000000)) * (126 / 100) + 2 * ((92854477 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12811) *
          (32 * (((223244657 / 12500000000000000000) : ℝ) + (317668637 / 25000000000000000000) + (92854477 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12811

/-! A coarse bound on the actual paper statistics constant at dimension 12812. -/
namespace BstLean.Part266.Row12812
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12810 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12810 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12810 128 ≤ (13064 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13064 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12812) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12812 : ℕ))
    (by norm_num : (12812 : ℕ) ≤ 16384)
  have ht : paperTail256 12812 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12812 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12812 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12812 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12812 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12812 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12810 128 * √(2 / (12812 : ℝ)) *
      (√(12812 : ℝ) + paperT0 12812 + paperTail256 12812) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12812 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12812 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12812 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12810 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12810 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12812 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12812

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12812
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12812 (61 / 100) 163 (17 / (100 * 12812)) (26 / (10 * 12812)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12812 (61 / 100) 163 (17 / (100 * 12812)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (29009941 / 6250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (181142313 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2383549039 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12812 / 12812 * (61 / 100)) ^ 4 * inverseRadius8 (12812 - 1) /
            envelopeGap 12812 (61 / 100) 163 (17 / (100 * 12812)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12812

namespace BstLean.Part266.Row12812
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12812 163 ≤ (1120800099 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12812 163 ≤ (747835703 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (71897029 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12812 163 ≤ (1785539681 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12812 163 ≤ (39699291 / 3125000000000000000)
  w2 : (tableEnvelope C).w2 12812 163 ≤ (232081837 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (29009941 / 6250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (29009941 / 6250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (181142313 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2383549039 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3642637 / 1000000000) : ℝ) ≤ √(17 / (100 * 12812) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12812) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2154435091 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9516887963 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12812) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12812) ≤ (862359 / 7812500000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12812) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12812 * (163 : ℝ) ^ 2 + 26 / (10 * 12812) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12812) : ℝ)) (tA 12812 * 163 ^ 2 + 26 / (10 * 12812)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3642637 / 1000000000))) * ((29009941 / 6250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3642637 / 1000000000)) ^ 3) * ((181142313 / 125000000000000000000000))) + ((2383549039 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3642637 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12812) : ℝ)) d.D d.V d.P (√(tA 12812) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3642637 / 1000000000)) ^ 2 * (((2154435091 / 1000000000000000)) * ((9516887963 / 250000000000000000)))) + ((2383549039 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12812) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3642637 / 1000000000)) * ((29009941 / 6250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12812) : ℝ)) (tA 12812 * 163 ^ 2 + 26 / (10 * 12812)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((29009941 / 6250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3642637 / 1000000000)) ^ 2) * ((181142313 / 125000000000000000000000)) + ((2383549039 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12812) : ℝ)) (√(26 / (10 * 12812) : ℝ)) d.D d.V d.P (√(tA 12812) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3642637 / 1000000000)) * (((2154435091 / 1000000000000000)) * ((9516887963 / 250000000000000000))) + ((2383549039 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12812) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((29009941 / 6250000000000000000) : ℝ) + ((2383549039 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12812

namespace BstLean.Part266.Row12812
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12812 163 ∧
    0 ≤ (tableEnvelope C).f1 12812 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12812 163 ∧
    0 ≤ (tableEnvelope C).w1 12812 163 ∧ 0 ≤ (tableEnvelope C).w2 12812 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12812 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12812 163 ∧ 0 ≤ d.f1 12812 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12812 163 ∧ 0 ≤ d.w1 12812 163 ∧ 0 ≤ d.w2 12812 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12812 ≤ 2 * (228 / 100 : ℝ) / 12812 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12812 ≤ 2 * (370 / 100 : ℝ) / 12812 := by
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
    (completeRAData (tableEnvelope C) 12812 163).locationBound 12812 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12812 163).energyBound 12812 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12812 163) (d.f1 12812 163) d.f2 ≤
      32 * (((1120800099 / 250000000000000000) : ℝ) + (747835703 / 500000000000000000) + (71897029 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12812 163) (d.w1 12812 163)
      (d.w2 12812 163) ≤
      32 * (((1785539681 / 100000000000000000000) : ℝ) + (39699291 / 3125000000000000000) + (232081837 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12812 163) (d.f1 12812 163) d.f2 ≤
      ((1120800099 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1120800099 / 250000000000000000)) * ((747835703 / 500000000000000000)) * (126 / 100) +
      2 * (((747835703 / 500000000000000000)) ^ 2 + 2 * ((1120800099 / 250000000000000000)) * ((71897029 / 200000000000000000))) +
      6 * ((747835703 / 500000000000000000)) * ((71897029 / 200000000000000000)) * (126 / 100) + 8 * ((71897029 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12812 163) (d.f1 12812 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12812 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12812 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12812 163) (d.f1 12812 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12812 163) (d.w1 12812 163) (d.w2 12812 163)
  have hwexpr0 : 0 ≤ d.w0 12812 163 + d.w1 12812 163 * √(π / 2) +
      2 * d.w2 12812 163 + energyR16 12812 *
      radiusPolynomialRoot16 (d.w0 12812 163) (d.w1 12812 163) (d.w2 12812 163) := by
    positivity
  constructor
  · change (12812 : ℝ) ^ 8 * (mA 12812 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12812 163) (d.f1 12812 163) d.f2 + locationR16 12812 *
        radiusPolynomialRoot16 (d.f0 12812 163) (d.f1 12812 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12812 : ℝ) ^ 8 * (mA 12812 : ℝ) ^ 8 *
        ((((1120800099 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1120800099 / 250000000000000000)) * ((747835703 / 500000000000000000)) * (126 / 100) +
          2 * (((747835703 / 500000000000000000)) ^ 2 + 2 * ((1120800099 / 250000000000000000)) * ((71897029 / 200000000000000000))) +
          6 * ((747835703 / 500000000000000000)) * ((71897029 / 200000000000000000)) * (126 / 100) + 8 * ((71897029 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12812) *
          (32 * (((1120800099 / 250000000000000000) : ℝ) + (747835703 / 500000000000000000) + (71897029 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12812 : ℝ) ^ 16 *
      (d.w0 12812 163 + d.w1 12812 163 * √(π / 2) + 2 * d.w2 12812 163 +
        energyR16 12812 * radiusPolynomialRoot16 (d.w0 12812 163) (d.w1 12812 163)
          (d.w2 12812 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12812 : ℝ) ^ 16 *
        (((1785539681 / 100000000000000000000) : ℝ) + ((39699291 / 3125000000000000000)) * (126 / 100) + 2 * ((232081837 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12812) *
          (32 * (((1785539681 / 100000000000000000000) : ℝ) + (39699291 / 3125000000000000000) + (232081837 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12812

/-! A coarse bound on the actual paper statistics constant at dimension 12813. -/
namespace BstLean.Part266.Row12813
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12811 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12811 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12811 128 ≤ (13065 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13065 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12813) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12813 : ℕ))
    (by norm_num : (12813 : ℕ) ≤ 16384)
  have ht : paperTail256 12813 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12813 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12813 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12813 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12813 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12813 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12811 128 * √(2 / (12813 : ℝ)) *
      (√(12813 : ℝ) + paperT0 12813 + paperTail256 12813) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12813 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12813 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12813 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12811 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12811 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12813 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12813

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12813
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12813 (61 / 100) 163 (17 / (100 * 12813)) (26 / (10 * 12813)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12813 (61 / 100) 163 (17 / (100 * 12813)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (232025191 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1448686143 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1191023501 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12813 / 12813 * (61 / 100)) ^ 4 * inverseRadius8 (12813 - 1) /
            envelopeGap 12813 (61 / 100) 163 (17 / (100 * 12813)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12813

namespace BstLean.Part266.Row12813
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12813 163 ≤ (4482325127 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12813 163 ≤ (2920663 / 1953125000000000)
  f2 : (tableEnvelope C).f2 ≤ (35941499 / 100000000000000000)
  w0 : (tableEnvelope C).w0 12813 163 ≤ (892560761 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12813 163 ≤ (79379989 / 6250000000000000000)
  w2 : (tableEnvelope C).w2 12813 163 ≤ (464054997 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (232025191 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (232025191 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1448686143 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1191023501 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((728499 / 200000000) : ℝ) ≤ √(17 / (100 * 12813) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12813) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1077091433 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4757701229 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12813) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12813) ≤ (110373337 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12813) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12813 * (163 : ℝ) ^ 2 + 26 / (10 * 12813) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12813) : ℝ)) (tA 12813 * 163 ^ 2 + 26 / (10 * 12813)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((728499 / 200000000))) * ((232025191 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((728499 / 200000000)) ^ 3) * ((1448686143 / 1000000000000000000000000))) + ((1191023501 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((728499 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12813) : ℝ)) d.D d.V d.P (√(tA 12813) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((728499 / 200000000)) ^ 2 * (((1077091433 / 500000000000000)) * ((4757701229 / 125000000000000000)))) + ((1191023501 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12813) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((728499 / 200000000)) * ((232025191 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12813) : ℝ)) (tA 12813 * 163 ^ 2 + 26 / (10 * 12813)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((232025191 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((728499 / 200000000)) ^ 2) * ((1448686143 / 1000000000000000000000000)) + ((1191023501 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12813) : ℝ)) (√(26 / (10 * 12813) : ℝ)) d.D d.V d.P (√(tA 12813) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((728499 / 200000000)) * (((1077091433 / 500000000000000)) * ((4757701229 / 125000000000000000))) + ((1191023501 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12813) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((232025191 / 50000000000000000000) : ℝ) + ((1191023501 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12813

namespace BstLean.Part266.Row12813
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12813 163 ∧
    0 ≤ (tableEnvelope C).f1 12813 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12813 163 ∧
    0 ≤ (tableEnvelope C).w1 12813 163 ∧ 0 ≤ (tableEnvelope C).w2 12813 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12813 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12813 163 ∧ 0 ≤ d.f1 12813 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12813 163 ∧ 0 ≤ d.w1 12813 163 ∧ 0 ≤ d.w2 12813 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12813 ≤ 2 * (228 / 100 : ℝ) / 12813 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12813 ≤ 2 * (370 / 100 : ℝ) / 12813 := by
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
    (completeRAData (tableEnvelope C) 12813 163).locationBound 12813 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12813 163).energyBound 12813 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12813 163) (d.f1 12813 163) d.f2 ≤
      32 * (((4482325127 / 1000000000000000000) : ℝ) + (2920663 / 1953125000000000) + (35941499 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12813 163) (d.w1 12813 163)
      (d.w2 12813 163) ≤
      32 * (((892560761 / 50000000000000000000) : ℝ) + (79379989 / 6250000000000000000) + (464054997 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12813 163) (d.f1 12813 163) d.f2 ≤
      ((4482325127 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4482325127 / 1000000000000000000)) * ((2920663 / 1953125000000000)) * (126 / 100) +
      2 * (((2920663 / 1953125000000000)) ^ 2 + 2 * ((4482325127 / 1000000000000000000)) * ((35941499 / 100000000000000000))) +
      6 * ((2920663 / 1953125000000000)) * ((35941499 / 100000000000000000)) * (126 / 100) + 8 * ((35941499 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12813 163) (d.f1 12813 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12813 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12813 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12813 163) (d.f1 12813 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12813 163) (d.w1 12813 163) (d.w2 12813 163)
  have hwexpr0 : 0 ≤ d.w0 12813 163 + d.w1 12813 163 * √(π / 2) +
      2 * d.w2 12813 163 + energyR16 12813 *
      radiusPolynomialRoot16 (d.w0 12813 163) (d.w1 12813 163) (d.w2 12813 163) := by
    positivity
  constructor
  · change (12813 : ℝ) ^ 8 * (mA 12813 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12813 163) (d.f1 12813 163) d.f2 + locationR16 12813 *
        radiusPolynomialRoot16 (d.f0 12813 163) (d.f1 12813 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12813 : ℝ) ^ 8 * (mA 12813 : ℝ) ^ 8 *
        ((((4482325127 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4482325127 / 1000000000000000000)) * ((2920663 / 1953125000000000)) * (126 / 100) +
          2 * (((2920663 / 1953125000000000)) ^ 2 + 2 * ((4482325127 / 1000000000000000000)) * ((35941499 / 100000000000000000))) +
          6 * ((2920663 / 1953125000000000)) * ((35941499 / 100000000000000000)) * (126 / 100) + 8 * ((35941499 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12813) *
          (32 * (((4482325127 / 1000000000000000000) : ℝ) + (2920663 / 1953125000000000) + (35941499 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12813 : ℝ) ^ 16 *
      (d.w0 12813 163 + d.w1 12813 163 * √(π / 2) + 2 * d.w2 12813 163 +
        energyR16 12813 * radiusPolynomialRoot16 (d.w0 12813 163) (d.w1 12813 163)
          (d.w2 12813 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12813 : ℝ) ^ 16 *
        (((892560761 / 50000000000000000000) : ℝ) + ((79379989 / 6250000000000000000)) * (126 / 100) + 2 * ((464054997 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12813) *
          (32 * (((892560761 / 50000000000000000000) : ℝ) + (79379989 / 6250000000000000000) + (464054997 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12813

/-! A coarse bound on the actual paper statistics constant at dimension 12814. -/
namespace BstLean.Part266.Row12814
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12812 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12812 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12812 128 ≤ (13066 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13066 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12814) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12814 : ℕ))
    (by norm_num : (12814 : ℕ) ≤ 16384)
  have ht : paperTail256 12814 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12814 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12814 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12814 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12814 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12814 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12812 128 * √(2 / (12814 : ℝ)) *
      (√(12814 : ℝ) + paperT0 12814 + paperTail256 12814) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12814 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12814 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12814 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12812 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12812 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12814 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12814

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12814
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12814 (61 / 100) 163 (17 / (100 * 12814)) (26 / (10 * 12814)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12814 (61 / 100) 163 (17 / (100 * 12814)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (231970871 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (724116979 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4761092063 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12814 / 12814 * (61 / 100)) ^ 4 * inverseRadius8 (12814 - 1) /
            envelopeGap 12814 (61 / 100) 163 (17 / (100 * 12814)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12814

namespace BstLean.Part266.Row12814
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12814 163 ≤ (896290031 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12814 163 ≤ (1495087599 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (71868971 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12814 163 ≤ (892351753 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12814 163 ≤ (317445609 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12814 163 ≤ (92789271 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (231970871 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (231970871 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (724116979 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4761092063 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3642353 / 1000000000) : ℝ) ≤ √(17 / (100 * 12814) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12814) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2153930691 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38055669197 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12814) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12814) ≤ (27591181 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12814) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12814 * (163 : ℝ) ^ 2 + 26 / (10 * 12814) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12814) : ℝ)) (tA 12814 * 163 ^ 2 + 26 / (10 * 12814)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3642353 / 1000000000))) * ((231970871 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3642353 / 1000000000)) ^ 3) * ((724116979 / 500000000000000000000000))) + ((4761092063 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3642353 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12814) : ℝ)) d.D d.V d.P (√(tA 12814) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3642353 / 1000000000)) ^ 2 * (((2153930691 / 1000000000000000)) * ((38055669197 / 1000000000000000000)))) + ((4761092063 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12814) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3642353 / 1000000000)) * ((231970871 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12814) : ℝ)) (tA 12814 * 163 ^ 2 + 26 / (10 * 12814)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((231970871 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3642353 / 1000000000)) ^ 2) * ((724116979 / 500000000000000000000000)) + ((4761092063 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12814) : ℝ)) (√(26 / (10 * 12814) : ℝ)) d.D d.V d.P (√(tA 12814) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3642353 / 1000000000)) * (((2153930691 / 1000000000000000)) * ((38055669197 / 1000000000000000000))) + ((4761092063 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12814) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((231970871 / 50000000000000000000) : ℝ) + ((4761092063 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12814

namespace BstLean.Part266.Row12814
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12814 163 ∧
    0 ≤ (tableEnvelope C).f1 12814 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12814 163 ∧
    0 ≤ (tableEnvelope C).w1 12814 163 ∧ 0 ≤ (tableEnvelope C).w2 12814 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12814 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12814 163 ∧ 0 ≤ d.f1 12814 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12814 163 ∧ 0 ≤ d.w1 12814 163 ∧ 0 ≤ d.w2 12814 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12814 ≤ 2 * (228 / 100 : ℝ) / 12814 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12814 ≤ 2 * (370 / 100 : ℝ) / 12814 := by
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
    (completeRAData (tableEnvelope C) 12814 163).locationBound 12814 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12814 163).energyBound 12814 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12814 163) (d.f1 12814 163) d.f2 ≤
      32 * (((896290031 / 200000000000000000) : ℝ) + (1495087599 / 1000000000000000000) + (71868971 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12814 163) (d.w1 12814 163)
      (d.w2 12814 163) ≤
      32 * (((892351753 / 50000000000000000000) : ℝ) + (317445609 / 25000000000000000000) + (92789271 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12814 163) (d.f1 12814 163) d.f2 ≤
      ((896290031 / 200000000000000000) : ℝ) ^ 2 + 2 * ((896290031 / 200000000000000000)) * ((1495087599 / 1000000000000000000)) * (126 / 100) +
      2 * (((1495087599 / 1000000000000000000)) ^ 2 + 2 * ((896290031 / 200000000000000000)) * ((71868971 / 200000000000000000))) +
      6 * ((1495087599 / 1000000000000000000)) * ((71868971 / 200000000000000000)) * (126 / 100) + 8 * ((71868971 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12814 163) (d.f1 12814 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12814 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12814 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12814 163) (d.f1 12814 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12814 163) (d.w1 12814 163) (d.w2 12814 163)
  have hwexpr0 : 0 ≤ d.w0 12814 163 + d.w1 12814 163 * √(π / 2) +
      2 * d.w2 12814 163 + energyR16 12814 *
      radiusPolynomialRoot16 (d.w0 12814 163) (d.w1 12814 163) (d.w2 12814 163) := by
    positivity
  constructor
  · change (12814 : ℝ) ^ 8 * (mA 12814 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12814 163) (d.f1 12814 163) d.f2 + locationR16 12814 *
        radiusPolynomialRoot16 (d.f0 12814 163) (d.f1 12814 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12814 : ℝ) ^ 8 * (mA 12814 : ℝ) ^ 8 *
        ((((896290031 / 200000000000000000) : ℝ) ^ 2 + 2 * ((896290031 / 200000000000000000)) * ((1495087599 / 1000000000000000000)) * (126 / 100) +
          2 * (((1495087599 / 1000000000000000000)) ^ 2 + 2 * ((896290031 / 200000000000000000)) * ((71868971 / 200000000000000000))) +
          6 * ((1495087599 / 1000000000000000000)) * ((71868971 / 200000000000000000)) * (126 / 100) + 8 * ((71868971 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12814) *
          (32 * (((896290031 / 200000000000000000) : ℝ) + (1495087599 / 1000000000000000000) + (71868971 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12814 : ℝ) ^ 16 *
      (d.w0 12814 163 + d.w1 12814 163 * √(π / 2) + 2 * d.w2 12814 163 +
        energyR16 12814 * radiusPolynomialRoot16 (d.w0 12814 163) (d.w1 12814 163)
          (d.w2 12814 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12814 : ℝ) ^ 16 *
        (((892351753 / 50000000000000000000) : ℝ) + ((317445609 / 25000000000000000000)) * (126 / 100) + 2 * ((92789271 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12814) *
          (32 * (((892351753 / 50000000000000000000) : ℝ) + (317445609 / 25000000000000000000) + (92789271 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12814

/-! A coarse bound on the actual paper statistics constant at dimension 12815. -/
namespace BstLean.Part266.Row12815
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12813 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12813 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12813 128 ≤ (13067 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13067 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12815) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12815 : ℕ))
    (by norm_num : (12815 : ℕ) ≤ 16384)
  have ht : paperTail256 12815 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12815 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12815 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12815 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12815 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12815 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12813 128 * √(2 / (12815 : ℝ)) *
      (√(12815 : ℝ) + paperT0 12815 + paperTail256 12815) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12815 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12815 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12815 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12813 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12813 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12815 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12815

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12815
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12815 (61 / 100) 163 (17 / (100 * 12815)) (26 / (10 * 12815)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12815 (61 / 100) 163 (17 / (100 * 12815)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (28989571 / 6250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (28955639 / 20000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4758092251 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12815 / 12815 * (61 / 100)) ^ 4 * inverseRadius8 (12815 - 1) /
            envelopeGap 12815 (61 / 100) 163 (17 / (100 * 12815)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12815

namespace BstLean.Part266.Row12815
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12815 163 ≤ (2240287741 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12815 163 ≤ (298959167 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (359274741 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12815 163 ≤ (27879463 / 1562500000000000000)
  w1 : (tableEnvelope C).w1 12815 163 ≤ (1269485147 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12815 163 ≤ (231918873 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (28989571 / 6250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (28989571 / 6250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (28955639 / 20000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4758092251 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3642211 / 1000000000) : ℝ) ≤ √(17 / (100 * 12815) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12815) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (430735713 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (951243249 / 25000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12815) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12815) ≤ (110356111 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12815) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12815 * (163 : ℝ) ^ 2 + 26 / (10 * 12815) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12815) : ℝ)) (tA 12815 * 163 ^ 2 + 26 / (10 * 12815)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3642211 / 1000000000))) * ((28989571 / 6250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3642211 / 1000000000)) ^ 3) * ((28955639 / 20000000000000000000000))) + ((4758092251 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3642211 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12815) : ℝ)) d.D d.V d.P (√(tA 12815) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3642211 / 1000000000)) ^ 2 * (((430735713 / 200000000000000)) * ((951243249 / 25000000000000000)))) + ((4758092251 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12815) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3642211 / 1000000000)) * ((28989571 / 6250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12815) : ℝ)) (tA 12815 * 163 ^ 2 + 26 / (10 * 12815)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((28989571 / 6250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3642211 / 1000000000)) ^ 2) * ((28955639 / 20000000000000000000000)) + ((4758092251 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12815) : ℝ)) (√(26 / (10 * 12815) : ℝ)) d.D d.V d.P (√(tA 12815) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3642211 / 1000000000)) * (((430735713 / 200000000000000)) * ((951243249 / 25000000000000000))) + ((4758092251 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12815) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((28989571 / 6250000000000000000) : ℝ) + ((4758092251 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12815

namespace BstLean.Part266.Row12815
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12815 163 ∧
    0 ≤ (tableEnvelope C).f1 12815 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12815 163 ∧
    0 ≤ (tableEnvelope C).w1 12815 163 ∧ 0 ≤ (tableEnvelope C).w2 12815 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12815 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12815 163 ∧ 0 ≤ d.f1 12815 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12815 163 ∧ 0 ≤ d.w1 12815 163 ∧ 0 ≤ d.w2 12815 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12815 ≤ 2 * (228 / 100 : ℝ) / 12815 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12815 ≤ 2 * (370 / 100 : ℝ) / 12815 := by
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
    (completeRAData (tableEnvelope C) 12815 163).locationBound 12815 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12815 163).energyBound 12815 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12815 163) (d.f1 12815 163) d.f2 ≤
      32 * (((2240287741 / 500000000000000000) : ℝ) + (298959167 / 200000000000000000) + (359274741 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12815 163) (d.w1 12815 163)
      (d.w2 12815 163) ≤
      32 * (((27879463 / 1562500000000000000) : ℝ) + (1269485147 / 100000000000000000000) + (231918873 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12815 163) (d.f1 12815 163) d.f2 ≤
      ((2240287741 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2240287741 / 500000000000000000)) * ((298959167 / 200000000000000000)) * (126 / 100) +
      2 * (((298959167 / 200000000000000000)) ^ 2 + 2 * ((2240287741 / 500000000000000000)) * ((359274741 / 1000000000000000000))) +
      6 * ((298959167 / 200000000000000000)) * ((359274741 / 1000000000000000000)) * (126 / 100) + 8 * ((359274741 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12815 163) (d.f1 12815 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12815 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12815 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12815 163) (d.f1 12815 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12815 163) (d.w1 12815 163) (d.w2 12815 163)
  have hwexpr0 : 0 ≤ d.w0 12815 163 + d.w1 12815 163 * √(π / 2) +
      2 * d.w2 12815 163 + energyR16 12815 *
      radiusPolynomialRoot16 (d.w0 12815 163) (d.w1 12815 163) (d.w2 12815 163) := by
    positivity
  constructor
  · change (12815 : ℝ) ^ 8 * (mA 12815 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12815 163) (d.f1 12815 163) d.f2 + locationR16 12815 *
        radiusPolynomialRoot16 (d.f0 12815 163) (d.f1 12815 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12815 : ℝ) ^ 8 * (mA 12815 : ℝ) ^ 8 *
        ((((2240287741 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2240287741 / 500000000000000000)) * ((298959167 / 200000000000000000)) * (126 / 100) +
          2 * (((298959167 / 200000000000000000)) ^ 2 + 2 * ((2240287741 / 500000000000000000)) * ((359274741 / 1000000000000000000))) +
          6 * ((298959167 / 200000000000000000)) * ((359274741 / 1000000000000000000)) * (126 / 100) + 8 * ((359274741 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12815) *
          (32 * (((2240287741 / 500000000000000000) : ℝ) + (298959167 / 200000000000000000) + (359274741 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12815 : ℝ) ^ 16 *
      (d.w0 12815 163 + d.w1 12815 163 * √(π / 2) + 2 * d.w2 12815 163 +
        energyR16 12815 * radiusPolynomialRoot16 (d.w0 12815 163) (d.w1 12815 163)
          (d.w2 12815 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12815 : ℝ) ^ 16 *
        (((27879463 / 1562500000000000000) : ℝ) + ((1269485147 / 100000000000000000000)) * (126 / 100) + 2 * ((231918873 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12815) *
          (32 * (((27879463 / 1562500000000000000) : ℝ) + (1269485147 / 100000000000000000000) + (231918873 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12815

/-! A coarse bound on the actual paper statistics constant at dimension 12816. -/
namespace BstLean.Part266.Row12816
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12814 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12814 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12814 128 ≤ (13068 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13068 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12816) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12816 : ℕ))
    (by norm_num : (12816 : ℕ) ≤ 16384)
  have ht : paperTail256 12816 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12816 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12816 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12816 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12816 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12816 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12814 128 * √(2 / (12816 : ℝ)) *
      (√(12816 : ℝ) + paperT0 12816 + paperTail256 12816) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12816 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12816 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12816 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12814 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12814 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12816 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12816

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12816
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12816 (61 / 100) 163 (17 / (100 * 12816)) (26 / (10 * 12816)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12816 (61 / 100) 163 (17 / (100 * 12816)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (463724563 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (723665059 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (594386821 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12816 / 12816 * (61 / 100)) ^ 4 * inverseRadius8 (12816 - 1) /
            envelopeGap 12816 (61 / 100) 163 (17 / (100 * 12816)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12816

namespace BstLean.Part266.Row12816
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12816 163 ≤ (2239850553 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12816 163 ≤ (373626041 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (359204647 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12816 163 ≤ (17838679 / 1000000000000000000)
  w1 : (tableEnvelope C).w1 12816 163 ≤ (253837591 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12816 163 ≤ (46372917 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (463724563 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (463724563 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (723665059 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (594386821 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3642069 / 1000000000) : ℝ) ≤ √(17 / (100 * 12816) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12816) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1076713243 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38043792109 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12816) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12816) ≤ (110347501 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12816) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12816 * (163 : ℝ) ^ 2 + 26 / (10 * 12816) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12816) : ℝ)) (tA 12816 * 163 ^ 2 + 26 / (10 * 12816)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3642069 / 1000000000))) * ((463724563 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3642069 / 1000000000)) ^ 3) * ((723665059 / 500000000000000000000000))) + ((594386821 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3642069 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12816) : ℝ)) d.D d.V d.P (√(tA 12816) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3642069 / 1000000000)) ^ 2 * (((1076713243 / 500000000000000)) * ((38043792109 / 1000000000000000000)))) + ((594386821 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12816) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3642069 / 1000000000)) * ((463724563 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12816) : ℝ)) (tA 12816 * 163 ^ 2 + 26 / (10 * 12816)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((463724563 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3642069 / 1000000000)) ^ 2) * ((723665059 / 500000000000000000000000)) + ((594386821 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12816) : ℝ)) (√(26 / (10 * 12816) : ℝ)) d.D d.V d.P (√(tA 12816) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3642069 / 1000000000)) * (((1076713243 / 500000000000000)) * ((38043792109 / 1000000000000000000))) + ((594386821 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12816) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((463724563 / 100000000000000000000) : ℝ) + ((594386821 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12816

namespace BstLean.Part266.Row12816
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12816 163 ∧
    0 ≤ (tableEnvelope C).f1 12816 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12816 163 ∧
    0 ≤ (tableEnvelope C).w1 12816 163 ∧ 0 ≤ (tableEnvelope C).w2 12816 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12816 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12816 163 ∧ 0 ≤ d.f1 12816 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12816 163 ∧ 0 ≤ d.w1 12816 163 ∧ 0 ≤ d.w2 12816 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12816 ≤ 2 * (228 / 100 : ℝ) / 12816 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12816 ≤ 2 * (370 / 100 : ℝ) / 12816 := by
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
    (completeRAData (tableEnvelope C) 12816 163).locationBound 12816 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12816 163).energyBound 12816 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12816 163) (d.f1 12816 163) d.f2 ≤
      32 * (((2239850553 / 500000000000000000) : ℝ) + (373626041 / 250000000000000000) + (359204647 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12816 163) (d.w1 12816 163)
      (d.w2 12816 163) ≤
      32 * (((17838679 / 1000000000000000000) : ℝ) + (253837591 / 20000000000000000000) + (46372917 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12816 163) (d.f1 12816 163) d.f2 ≤
      ((2239850553 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2239850553 / 500000000000000000)) * ((373626041 / 250000000000000000)) * (126 / 100) +
      2 * (((373626041 / 250000000000000000)) ^ 2 + 2 * ((2239850553 / 500000000000000000)) * ((359204647 / 1000000000000000000))) +
      6 * ((373626041 / 250000000000000000)) * ((359204647 / 1000000000000000000)) * (126 / 100) + 8 * ((359204647 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12816 163) (d.f1 12816 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12816 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12816 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12816 163) (d.f1 12816 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12816 163) (d.w1 12816 163) (d.w2 12816 163)
  have hwexpr0 : 0 ≤ d.w0 12816 163 + d.w1 12816 163 * √(π / 2) +
      2 * d.w2 12816 163 + energyR16 12816 *
      radiusPolynomialRoot16 (d.w0 12816 163) (d.w1 12816 163) (d.w2 12816 163) := by
    positivity
  constructor
  · change (12816 : ℝ) ^ 8 * (mA 12816 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12816 163) (d.f1 12816 163) d.f2 + locationR16 12816 *
        radiusPolynomialRoot16 (d.f0 12816 163) (d.f1 12816 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12816 : ℝ) ^ 8 * (mA 12816 : ℝ) ^ 8 *
        ((((2239850553 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2239850553 / 500000000000000000)) * ((373626041 / 250000000000000000)) * (126 / 100) +
          2 * (((373626041 / 250000000000000000)) ^ 2 + 2 * ((2239850553 / 500000000000000000)) * ((359204647 / 1000000000000000000))) +
          6 * ((373626041 / 250000000000000000)) * ((359204647 / 1000000000000000000)) * (126 / 100) + 8 * ((359204647 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12816) *
          (32 * (((2239850553 / 500000000000000000) : ℝ) + (373626041 / 250000000000000000) + (359204647 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12816 : ℝ) ^ 16 *
      (d.w0 12816 163 + d.w1 12816 163 * √(π / 2) + 2 * d.w2 12816 163 +
        energyR16 12816 * radiusPolynomialRoot16 (d.w0 12816 163) (d.w1 12816 163)
          (d.w2 12816 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12816 : ℝ) ^ 16 *
        (((17838679 / 1000000000000000000) : ℝ) + ((253837591 / 20000000000000000000)) * (126 / 100) + 2 * ((46372917 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12816) *
          (32 * (((17838679 / 1000000000000000000) : ℝ) + (253837591 / 20000000000000000000) + (46372917 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12816

/-! A coarse bound on the actual paper statistics constant at dimension 12817. -/
namespace BstLean.Part266.Row12817
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12815 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12815 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12815 128 ≤ (13069 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13069 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12817) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12817 : ℕ))
    (by norm_num : (12817 : ℕ) ≤ 16384)
  have ht : paperTail256 12817 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12817 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12817 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12817 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12817 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12817 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12815 128 * √(2 / (12817 : ℝ)) *
      (√(12817 : ℝ) + paperT0 12817 + paperTail256 12817) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12817 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12817 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12817 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12815 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12815 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12817 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12817

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12817
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12817 (61 / 100) 163 (17 / (100 * 12817)) (26 / (10 * 12817)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12817 (61 / 100) 163 (17 / (100 * 12817)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (18544641 / 4000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1446878463 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4752099011 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12817 / 12817 * (61 / 100)) ^ 4 * inverseRadius8 (12817 - 1) /
            envelopeGap 12817 (61 / 100) 163 (17 / (100 * 12817)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12817

namespace BstLean.Part266.Row12817
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12817 163 ≤ (4478827031 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12817 163 ≤ (373553147 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (14365383 / 40000000000000000)
  w0 : (tableEnvelope C).w0 12817 163 ≤ (222931289 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 12817 163 ≤ (1268890863 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12817 163 ≤ (463620629 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (18544641 / 4000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (18544641 / 4000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1446878463 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4752099011 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3641927 / 1000000000) : ℝ) ≤ √(17 / (100 * 12817) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12817) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2153174459 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19018927829 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12817) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12817) ≤ (110338891 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12817) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12817 * (163 : ℝ) ^ 2 + 26 / (10 * 12817) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12817) : ℝ)) (tA 12817 * 163 ^ 2 + 26 / (10 * 12817)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3641927 / 1000000000))) * ((18544641 / 4000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3641927 / 1000000000)) ^ 3) * ((1446878463 / 1000000000000000000000000))) + ((4752099011 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3641927 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12817) : ℝ)) d.D d.V d.P (√(tA 12817) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3641927 / 1000000000)) ^ 2 * (((2153174459 / 1000000000000000)) * ((19018927829 / 500000000000000000)))) + ((4752099011 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12817) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3641927 / 1000000000)) * ((18544641 / 4000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12817) : ℝ)) (tA 12817 * 163 ^ 2 + 26 / (10 * 12817)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((18544641 / 4000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3641927 / 1000000000)) ^ 2) * ((1446878463 / 1000000000000000000000000)) + ((4752099011 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12817) : ℝ)) (√(26 / (10 * 12817) : ℝ)) d.D d.V d.P (√(tA 12817) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3641927 / 1000000000)) * (((2153174459 / 1000000000000000)) * ((19018927829 / 500000000000000000))) + ((4752099011 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12817) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((18544641 / 4000000000000000000) : ℝ) + ((4752099011 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12817

namespace BstLean.Part266.Row12817
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12817 163 ∧
    0 ≤ (tableEnvelope C).f1 12817 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12817 163 ∧
    0 ≤ (tableEnvelope C).w1 12817 163 ∧ 0 ≤ (tableEnvelope C).w2 12817 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12817 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12817 163 ∧ 0 ≤ d.f1 12817 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12817 163 ∧ 0 ≤ d.w1 12817 163 ∧ 0 ≤ d.w2 12817 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12817 ≤ 2 * (228 / 100 : ℝ) / 12817 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12817 ≤ 2 * (370 / 100 : ℝ) / 12817 := by
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
    (completeRAData (tableEnvelope C) 12817 163).locationBound 12817 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12817 163).energyBound 12817 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12817 163) (d.f1 12817 163) d.f2 ≤
      32 * (((4478827031 / 1000000000000000000) : ℝ) + (373553147 / 250000000000000000) + (14365383 / 40000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12817 163) (d.w1 12817 163)
      (d.w2 12817 163) ≤
      32 * (((222931289 / 12500000000000000000) : ℝ) + (1268890863 / 100000000000000000000) + (463620629 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12817 163) (d.f1 12817 163) d.f2 ≤
      ((4478827031 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4478827031 / 1000000000000000000)) * ((373553147 / 250000000000000000)) * (126 / 100) +
      2 * (((373553147 / 250000000000000000)) ^ 2 + 2 * ((4478827031 / 1000000000000000000)) * ((14365383 / 40000000000000000))) +
      6 * ((373553147 / 250000000000000000)) * ((14365383 / 40000000000000000)) * (126 / 100) + 8 * ((14365383 / 40000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12817 163) (d.f1 12817 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12817 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12817 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12817 163) (d.f1 12817 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12817 163) (d.w1 12817 163) (d.w2 12817 163)
  have hwexpr0 : 0 ≤ d.w0 12817 163 + d.w1 12817 163 * √(π / 2) +
      2 * d.w2 12817 163 + energyR16 12817 *
      radiusPolynomialRoot16 (d.w0 12817 163) (d.w1 12817 163) (d.w2 12817 163) := by
    positivity
  constructor
  · change (12817 : ℝ) ^ 8 * (mA 12817 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12817 163) (d.f1 12817 163) d.f2 + locationR16 12817 *
        radiusPolynomialRoot16 (d.f0 12817 163) (d.f1 12817 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12817 : ℝ) ^ 8 * (mA 12817 : ℝ) ^ 8 *
        ((((4478827031 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4478827031 / 1000000000000000000)) * ((373553147 / 250000000000000000)) * (126 / 100) +
          2 * (((373553147 / 250000000000000000)) ^ 2 + 2 * ((4478827031 / 1000000000000000000)) * ((14365383 / 40000000000000000))) +
          6 * ((373553147 / 250000000000000000)) * ((14365383 / 40000000000000000)) * (126 / 100) + 8 * ((14365383 / 40000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12817) *
          (32 * (((4478827031 / 1000000000000000000) : ℝ) + (373553147 / 250000000000000000) + (14365383 / 40000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12817 : ℝ) ^ 16 *
      (d.w0 12817 163 + d.w1 12817 163 * √(π / 2) + 2 * d.w2 12817 163 +
        energyR16 12817 * radiusPolynomialRoot16 (d.w0 12817 163) (d.w1 12817 163)
          (d.w2 12817 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12817 : ℝ) ^ 16 *
        (((222931289 / 12500000000000000000) : ℝ) + ((1268890863 / 100000000000000000000)) * (126 / 100) + 2 * ((463620629 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12817) *
          (32 * (((222931289 / 12500000000000000000) : ℝ) + (1268890863 / 100000000000000000000) + (463620629 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12817

/-! A coarse bound on the actual paper statistics constant at dimension 12818. -/
namespace BstLean.Part266.Row12818
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12816 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12816 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12816 128 ≤ (13070 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13070 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12818) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12818 : ℕ))
    (by norm_num : (12818 : ℕ) ≤ 16384)
  have ht : paperTail256 12818 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12818 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12818 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12818 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12818 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12818 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12816 128 * √(2 / (12818 : ℝ)) *
      (√(12818 : ℝ) + paperT0 12818 + paperTail256 12818) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12818 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12818 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12818 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12816 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12816 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12818 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12818

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12818
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12818 (61 / 100) 163 (17 / (100 * 12818)) (26 / (10 * 12818)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12818 (61 / 100) 163 (17 / (100 * 12818)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (1448461 / 312500000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (180803373 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4749105579 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12818 / 12818 * (61 / 100)) ^ 4 * inverseRadius8 (12818 - 1) /
            envelopeGap 12818 (61 / 100) 163 (17 / (100 * 12818)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12818

namespace BstLean.Part266.Row12818
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12818 163 ≤ (1119488313 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12818 163 ≤ (1493921103 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (359064523 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12818 163 ≤ (891516433 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12818 163 ≤ (317148467 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12818 163 ≤ (463512121 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (1448461 / 312500000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (1448461 / 312500000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (180803373 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4749105579 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((728357 / 200000000) : ℝ) ≤ √(17 / (100 * 12818) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12818) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2152922479 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19015960297 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12818) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12818) ≤ (110330283 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12818) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12818 * (163 : ℝ) ^ 2 + 26 / (10 * 12818) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12818) : ℝ)) (tA 12818 * 163 ^ 2 + 26 / (10 * 12818)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((728357 / 200000000))) * ((1448461 / 312500000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((728357 / 200000000)) ^ 3) * ((180803373 / 125000000000000000000000))) + ((4749105579 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((728357 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12818) : ℝ)) d.D d.V d.P (√(tA 12818) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((728357 / 200000000)) ^ 2 * (((2152922479 / 1000000000000000)) * ((19015960297 / 500000000000000000)))) + ((4749105579 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12818) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((728357 / 200000000)) * ((1448461 / 312500000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12818) : ℝ)) (tA 12818 * 163 ^ 2 + 26 / (10 * 12818)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((1448461 / 312500000000000000) : ℝ) + (24198 / 100000) / (2 * ((728357 / 200000000)) ^ 2) * ((180803373 / 125000000000000000000000)) + ((4749105579 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12818) : ℝ)) (√(26 / (10 * 12818) : ℝ)) d.D d.V d.P (√(tA 12818) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((728357 / 200000000)) * (((2152922479 / 1000000000000000)) * ((19015960297 / 500000000000000000))) + ((4749105579 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12818) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((1448461 / 312500000000000000) : ℝ) + ((4749105579 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12818

namespace BstLean.Part266.Row12818
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12818 163 ∧
    0 ≤ (tableEnvelope C).f1 12818 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12818 163 ∧
    0 ≤ (tableEnvelope C).w1 12818 163 ∧ 0 ≤ (tableEnvelope C).w2 12818 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12818 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12818 163 ∧ 0 ≤ d.f1 12818 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12818 163 ∧ 0 ≤ d.w1 12818 163 ∧ 0 ≤ d.w2 12818 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12818 ≤ 2 * (228 / 100 : ℝ) / 12818 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12818 ≤ 2 * (370 / 100 : ℝ) / 12818 := by
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
    (completeRAData (tableEnvelope C) 12818 163).locationBound 12818 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12818 163).energyBound 12818 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12818 163) (d.f1 12818 163) d.f2 ≤
      32 * (((1119488313 / 250000000000000000) : ℝ) + (1493921103 / 1000000000000000000) + (359064523 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12818 163) (d.w1 12818 163)
      (d.w2 12818 163) ≤
      32 * (((891516433 / 50000000000000000000) : ℝ) + (317148467 / 25000000000000000000) + (463512121 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12818 163) (d.f1 12818 163) d.f2 ≤
      ((1119488313 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1119488313 / 250000000000000000)) * ((1493921103 / 1000000000000000000)) * (126 / 100) +
      2 * (((1493921103 / 1000000000000000000)) ^ 2 + 2 * ((1119488313 / 250000000000000000)) * ((359064523 / 1000000000000000000))) +
      6 * ((1493921103 / 1000000000000000000)) * ((359064523 / 1000000000000000000)) * (126 / 100) + 8 * ((359064523 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12818 163) (d.f1 12818 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12818 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12818 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12818 163) (d.f1 12818 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12818 163) (d.w1 12818 163) (d.w2 12818 163)
  have hwexpr0 : 0 ≤ d.w0 12818 163 + d.w1 12818 163 * √(π / 2) +
      2 * d.w2 12818 163 + energyR16 12818 *
      radiusPolynomialRoot16 (d.w0 12818 163) (d.w1 12818 163) (d.w2 12818 163) := by
    positivity
  constructor
  · change (12818 : ℝ) ^ 8 * (mA 12818 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12818 163) (d.f1 12818 163) d.f2 + locationR16 12818 *
        radiusPolynomialRoot16 (d.f0 12818 163) (d.f1 12818 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12818 : ℝ) ^ 8 * (mA 12818 : ℝ) ^ 8 *
        ((((1119488313 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1119488313 / 250000000000000000)) * ((1493921103 / 1000000000000000000)) * (126 / 100) +
          2 * (((1493921103 / 1000000000000000000)) ^ 2 + 2 * ((1119488313 / 250000000000000000)) * ((359064523 / 1000000000000000000))) +
          6 * ((1493921103 / 1000000000000000000)) * ((359064523 / 1000000000000000000)) * (126 / 100) + 8 * ((359064523 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12818) *
          (32 * (((1119488313 / 250000000000000000) : ℝ) + (1493921103 / 1000000000000000000) + (359064523 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12818 : ℝ) ^ 16 *
      (d.w0 12818 163 + d.w1 12818 163 * √(π / 2) + 2 * d.w2 12818 163 +
        energyR16 12818 * radiusPolynomialRoot16 (d.w0 12818 163) (d.w1 12818 163)
          (d.w2 12818 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12818 : ℝ) ^ 16 *
        (((891516433 / 50000000000000000000) : ℝ) + ((317148467 / 25000000000000000000)) * (126 / 100) + 2 * ((463512121 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12818) *
          (32 * (((891516433 / 50000000000000000000) : ℝ) + (317148467 / 25000000000000000000) + (463512121 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12818

/-! A coarse bound on the actual paper statistics constant at dimension 12819. -/
namespace BstLean.Part266.Row12819
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12817 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12817 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12817 128 ≤ (13071 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13071 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12819) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12819 : ℕ))
    (by norm_num : (12819 : ℕ) ≤ 16384)
  have ht : paperTail256 12819 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12819 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12819 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12819 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12819 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12819 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12817 128 * √(2 / (12819 : ℝ)) *
      (√(12819 : ℝ) + paperT0 12819 + paperTail256 12819) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12819 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12819 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12819 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12817 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12817 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12819 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12819

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12819
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12819 (61 / 100) 163 (17 / (100 * 12819)) (26 / (10 * 12819)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12819 (61 / 100) 163 (17 / (100 * 12819)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (9267981 / 2000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (2259337 / 1562500000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4746114271 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12819 / 12819 * (61 / 100)) ^ 4 * inverseRadius8 (12819 - 1) /
            envelopeGap 12819 (61 / 100) 163 (17 / (100 * 12819)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12819

namespace BstLean.Part266.Row12819
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12819 163 ≤ (559634971 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12819 163 ≤ (746814857 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (358994493 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12819 163 ≤ (891307781 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12819 163 ≤ (1268296973 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12819 163 ≤ (3620341 / 781250000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (9267981 / 2000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (9267981 / 2000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (2259337 / 1562500000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4746114271 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3641643 / 1000000000) : ℝ) ≤ √(17 / (100 * 12819) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12819) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2152670551 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4753248363 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12819) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12819) ≤ (27580419 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12819) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12819 * (163 : ℝ) ^ 2 + 26 / (10 * 12819) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12819) : ℝ)) (tA 12819 * 163 ^ 2 + 26 / (10 * 12819)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3641643 / 1000000000))) * ((9267981 / 2000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3641643 / 1000000000)) ^ 3) * ((2259337 / 1562500000000000000000))) + ((4746114271 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3641643 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12819) : ℝ)) d.D d.V d.P (√(tA 12819) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3641643 / 1000000000)) ^ 2 * (((2152670551 / 1000000000000000)) * ((4753248363 / 125000000000000000)))) + ((4746114271 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12819) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3641643 / 1000000000)) * ((9267981 / 2000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12819) : ℝ)) (tA 12819 * 163 ^ 2 + 26 / (10 * 12819)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((9267981 / 2000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3641643 / 1000000000)) ^ 2) * ((2259337 / 1562500000000000000000)) + ((4746114271 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12819) : ℝ)) (√(26 / (10 * 12819) : ℝ)) d.D d.V d.P (√(tA 12819) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3641643 / 1000000000)) * (((2152670551 / 1000000000000000)) * ((4753248363 / 125000000000000000))) + ((4746114271 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12819) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((9267981 / 2000000000000000000) : ℝ) + ((4746114271 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12819

namespace BstLean.Part266.Row12819
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12819 163 ∧
    0 ≤ (tableEnvelope C).f1 12819 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12819 163 ∧
    0 ≤ (tableEnvelope C).w1 12819 163 ∧ 0 ≤ (tableEnvelope C).w2 12819 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12819 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12819 163 ∧ 0 ≤ d.f1 12819 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12819 163 ∧ 0 ≤ d.w1 12819 163 ∧ 0 ≤ d.w2 12819 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12819 ≤ 2 * (228 / 100 : ℝ) / 12819 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12819 ≤ 2 * (370 / 100 : ℝ) / 12819 := by
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
    (completeRAData (tableEnvelope C) 12819 163).locationBound 12819 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12819 163).energyBound 12819 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12819 163) (d.f1 12819 163) d.f2 ≤
      32 * (((559634971 / 125000000000000000) : ℝ) + (746814857 / 500000000000000000) + (358994493 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12819 163) (d.w1 12819 163)
      (d.w2 12819 163) ≤
      32 * (((891307781 / 50000000000000000000) : ℝ) + (1268296973 / 100000000000000000000) + (3620341 / 781250000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12819 163) (d.f1 12819 163) d.f2 ≤
      ((559634971 / 125000000000000000) : ℝ) ^ 2 + 2 * ((559634971 / 125000000000000000)) * ((746814857 / 500000000000000000)) * (126 / 100) +
      2 * (((746814857 / 500000000000000000)) ^ 2 + 2 * ((559634971 / 125000000000000000)) * ((358994493 / 1000000000000000000))) +
      6 * ((746814857 / 500000000000000000)) * ((358994493 / 1000000000000000000)) * (126 / 100) + 8 * ((358994493 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12819 163) (d.f1 12819 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12819 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12819 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12819 163) (d.f1 12819 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12819 163) (d.w1 12819 163) (d.w2 12819 163)
  have hwexpr0 : 0 ≤ d.w0 12819 163 + d.w1 12819 163 * √(π / 2) +
      2 * d.w2 12819 163 + energyR16 12819 *
      radiusPolynomialRoot16 (d.w0 12819 163) (d.w1 12819 163) (d.w2 12819 163) := by
    positivity
  constructor
  · change (12819 : ℝ) ^ 8 * (mA 12819 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12819 163) (d.f1 12819 163) d.f2 + locationR16 12819 *
        radiusPolynomialRoot16 (d.f0 12819 163) (d.f1 12819 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12819 : ℝ) ^ 8 * (mA 12819 : ℝ) ^ 8 *
        ((((559634971 / 125000000000000000) : ℝ) ^ 2 + 2 * ((559634971 / 125000000000000000)) * ((746814857 / 500000000000000000)) * (126 / 100) +
          2 * (((746814857 / 500000000000000000)) ^ 2 + 2 * ((559634971 / 125000000000000000)) * ((358994493 / 1000000000000000000))) +
          6 * ((746814857 / 500000000000000000)) * ((358994493 / 1000000000000000000)) * (126 / 100) + 8 * ((358994493 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12819) *
          (32 * (((559634971 / 125000000000000000) : ℝ) + (746814857 / 500000000000000000) + (358994493 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12819 : ℝ) ^ 16 *
      (d.w0 12819 163 + d.w1 12819 163 * √(π / 2) + 2 * d.w2 12819 163 +
        energyR16 12819 * radiusPolynomialRoot16 (d.w0 12819 163) (d.w1 12819 163)
          (d.w2 12819 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12819 : ℝ) ^ 16 *
        (((891307781 / 50000000000000000000) : ℝ) + ((1268296973 / 100000000000000000000)) * (126 / 100) + 2 * ((3620341 / 781250000000000000)) +
          (2 * (370 / 100 : ℝ) / 12819) *
          (32 * (((891307781 / 50000000000000000000) : ℝ) + (1268296973 / 100000000000000000000) + (3620341 / 781250000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12819

/-! A coarse bound on the actual paper statistics constant at dimension 12820. -/
namespace BstLean.Part266.Row12820
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12818 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12818 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12818 128 ≤ (13072 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13072 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12820) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12820 : ℕ))
    (by norm_num : (12820 : ℕ) ≤ 16384)
  have ht : paperTail256 12820 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12820 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12820 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12820 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12820 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12820 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12818 128 * √(2 / (12820 : ℝ)) *
      (√(12820 : ℝ) + paperT0 12820 + paperTail256 12820) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12820 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12820 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12820 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12818 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12818 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12820 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12820

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12820
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12820 (61 / 100) 163 (17 / (100 * 12820)) (26 / (10 * 12820)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12820 (61 / 100) 163 (17 / (100 * 12820)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (463290613 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1445524553 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1185781271 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12820 / 12820 * (61 / 100)) ^ 4 * inverseRadius8 (12820 - 1) /
            envelopeGap 12820 (61 / 100) 163 (17 / (100 * 12820)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12820

namespace BstLean.Part266.Row12820
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12820 163 ≤ (895241317 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12820 163 ≤ (93333651 / 62500000000000000)
  f2 : (tableEnvelope C).f2 ≤ (358924483 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12820 163 ≤ (556937 / 31250000000000000)
  w1 : (tableEnvelope C).w1 12820 163 ≤ (79250011 / 6250000000000000000)
  w2 : (tableEnvelope C).w2 12820 163 ≤ (57911901 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (463290613 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (463290613 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1445524553 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1185781271 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3641501 / 1000000000) : ℝ) ≤ √(17 / (100 * 12820) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12820) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (215241867 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4752506827 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12820) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12820) ≤ (110313071 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12820) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12820 * (163 : ℝ) ^ 2 + 26 / (10 * 12820) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12820) : ℝ)) (tA 12820 * 163 ^ 2 + 26 / (10 * 12820)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3641501 / 1000000000))) * ((463290613 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3641501 / 1000000000)) ^ 3) * ((1445524553 / 1000000000000000000000000))) + ((1185781271 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3641501 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12820) : ℝ)) d.D d.V d.P (√(tA 12820) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3641501 / 1000000000)) ^ 2 * (((215241867 / 100000000000000)) * ((4752506827 / 125000000000000000)))) + ((1185781271 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12820) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3641501 / 1000000000)) * ((463290613 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12820) : ℝ)) (tA 12820 * 163 ^ 2 + 26 / (10 * 12820)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((463290613 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3641501 / 1000000000)) ^ 2) * ((1445524553 / 1000000000000000000000000)) + ((1185781271 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12820) : ℝ)) (√(26 / (10 * 12820) : ℝ)) d.D d.V d.P (√(tA 12820) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3641501 / 1000000000)) * (((215241867 / 100000000000000)) * ((4752506827 / 125000000000000000))) + ((1185781271 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12820) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((463290613 / 100000000000000000000) : ℝ) + ((1185781271 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12820

namespace BstLean.Part266.Row12820
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12820 163 ∧
    0 ≤ (tableEnvelope C).f1 12820 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12820 163 ∧
    0 ≤ (tableEnvelope C).w1 12820 163 ∧ 0 ≤ (tableEnvelope C).w2 12820 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12820 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12820 163 ∧ 0 ≤ d.f1 12820 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12820 163 ∧ 0 ≤ d.w1 12820 163 ∧ 0 ≤ d.w2 12820 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12820 ≤ 2 * (228 / 100 : ℝ) / 12820 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12820 ≤ 2 * (370 / 100 : ℝ) / 12820 := by
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
    (completeRAData (tableEnvelope C) 12820 163).locationBound 12820 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12820 163).energyBound 12820 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12820 163) (d.f1 12820 163) d.f2 ≤
      32 * (((895241317 / 200000000000000000) : ℝ) + (93333651 / 62500000000000000) + (358924483 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12820 163) (d.w1 12820 163)
      (d.w2 12820 163) ≤
      32 * (((556937 / 31250000000000000) : ℝ) + (79250011 / 6250000000000000000) + (57911901 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12820 163) (d.f1 12820 163) d.f2 ≤
      ((895241317 / 200000000000000000) : ℝ) ^ 2 + 2 * ((895241317 / 200000000000000000)) * ((93333651 / 62500000000000000)) * (126 / 100) +
      2 * (((93333651 / 62500000000000000)) ^ 2 + 2 * ((895241317 / 200000000000000000)) * ((358924483 / 1000000000000000000))) +
      6 * ((93333651 / 62500000000000000)) * ((358924483 / 1000000000000000000)) * (126 / 100) + 8 * ((358924483 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12820 163) (d.f1 12820 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12820 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12820 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12820 163) (d.f1 12820 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12820 163) (d.w1 12820 163) (d.w2 12820 163)
  have hwexpr0 : 0 ≤ d.w0 12820 163 + d.w1 12820 163 * √(π / 2) +
      2 * d.w2 12820 163 + energyR16 12820 *
      radiusPolynomialRoot16 (d.w0 12820 163) (d.w1 12820 163) (d.w2 12820 163) := by
    positivity
  constructor
  · change (12820 : ℝ) ^ 8 * (mA 12820 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12820 163) (d.f1 12820 163) d.f2 + locationR16 12820 *
        radiusPolynomialRoot16 (d.f0 12820 163) (d.f1 12820 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12820 : ℝ) ^ 8 * (mA 12820 : ℝ) ^ 8 *
        ((((895241317 / 200000000000000000) : ℝ) ^ 2 + 2 * ((895241317 / 200000000000000000)) * ((93333651 / 62500000000000000)) * (126 / 100) +
          2 * (((93333651 / 62500000000000000)) ^ 2 + 2 * ((895241317 / 200000000000000000)) * ((358924483 / 1000000000000000000))) +
          6 * ((93333651 / 62500000000000000)) * ((358924483 / 1000000000000000000)) * (126 / 100) + 8 * ((358924483 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12820) *
          (32 * (((895241317 / 200000000000000000) : ℝ) + (93333651 / 62500000000000000) + (358924483 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12820 : ℝ) ^ 16 *
      (d.w0 12820 163 + d.w1 12820 163 * √(π / 2) + 2 * d.w2 12820 163 +
        energyR16 12820 * radiusPolynomialRoot16 (d.w0 12820 163) (d.w1 12820 163)
          (d.w2 12820 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12820 : ℝ) ^ 16 *
        (((556937 / 31250000000000000) : ℝ) + ((79250011 / 6250000000000000000)) * (126 / 100) + 2 * ((57911901 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12820) *
          (32 * (((556937 / 31250000000000000) : ℝ) + (79250011 / 6250000000000000000) + (57911901 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12820

/-! A coarse bound on the actual paper statistics constant at dimension 12821. -/
namespace BstLean.Part266.Row12821
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12819 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12819 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12819 128 ≤ (13073 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13073 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12821) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12821 : ℕ))
    (by norm_num : (12821 : ℕ) ≤ 16384)
  have ht : paperTail256 12821 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12821 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12821 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12821 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12821 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12821 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12819 128 * √(2 / (12821 : ℝ)) *
      (√(12821 : ℝ) + paperT0 12821 + paperTail256 12821) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12821 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12821 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12821 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12819 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12819 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12821 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12821

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12821
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12821 (61 / 100) 163 (17 / (100 * 12821)) (26 / (10 * 12821)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12821 (61 / 100) 163 (17 / (100 * 12821)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (46318221 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (722536801 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4740138017 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12821 / 12821 * (61 / 100)) ^ 4 * inverseRadius8 (12821 - 1) /
            envelopeGap 12821 (61 / 100) 163 (17 / (100 * 12821)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12821

namespace BstLean.Part266.Row12821
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12821 163 ≤ (2237666849 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12821 163 ≤ (373261803 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (358854493 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12821 163 ≤ (1781781381 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12821 163 ≤ (633851739 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12821 163 ≤ (231593401 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (46318221 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (46318221 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (722536801 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4740138017 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3641359 / 1000000000) : ℝ) ≤ √(17 / (100 * 12821) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12821) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2152166839 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19007061859 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12821) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12821) ≤ (110304467 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12821) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12821 * (163 : ℝ) ^ 2 + 26 / (10 * 12821) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12821) : ℝ)) (tA 12821 * 163 ^ 2 + 26 / (10 * 12821)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3641359 / 1000000000))) * ((46318221 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3641359 / 1000000000)) ^ 3) * ((722536801 / 500000000000000000000000))) + ((4740138017 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3641359 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12821) : ℝ)) d.D d.V d.P (√(tA 12821) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3641359 / 1000000000)) ^ 2 * (((2152166839 / 1000000000000000)) * ((19007061859 / 500000000000000000)))) + ((4740138017 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12821) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3641359 / 1000000000)) * ((46318221 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12821) : ℝ)) (tA 12821 * 163 ^ 2 + 26 / (10 * 12821)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((46318221 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3641359 / 1000000000)) ^ 2) * ((722536801 / 500000000000000000000000)) + ((4740138017 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12821) : ℝ)) (√(26 / (10 * 12821) : ℝ)) d.D d.V d.P (√(tA 12821) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3641359 / 1000000000)) * (((2152166839 / 1000000000000000)) * ((19007061859 / 500000000000000000))) + ((4740138017 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12821) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((46318221 / 10000000000000000000) : ℝ) + ((4740138017 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12821

namespace BstLean.Part266.Row12821
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12821 163 ∧
    0 ≤ (tableEnvelope C).f1 12821 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12821 163 ∧
    0 ≤ (tableEnvelope C).w1 12821 163 ∧ 0 ≤ (tableEnvelope C).w2 12821 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12821 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12821 163 ∧ 0 ≤ d.f1 12821 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12821 163 ∧ 0 ≤ d.w1 12821 163 ∧ 0 ≤ d.w2 12821 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12821 ≤ 2 * (228 / 100 : ℝ) / 12821 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12821 ≤ 2 * (370 / 100 : ℝ) / 12821 := by
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
    (completeRAData (tableEnvelope C) 12821 163).locationBound 12821 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12821 163).energyBound 12821 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12821 163) (d.f1 12821 163) d.f2 ≤
      32 * (((2237666849 / 500000000000000000) : ℝ) + (373261803 / 250000000000000000) + (358854493 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12821 163) (d.w1 12821 163)
      (d.w2 12821 163) ≤
      32 * (((1781781381 / 100000000000000000000) : ℝ) + (633851739 / 50000000000000000000) + (231593401 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12821 163) (d.f1 12821 163) d.f2 ≤
      ((2237666849 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2237666849 / 500000000000000000)) * ((373261803 / 250000000000000000)) * (126 / 100) +
      2 * (((373261803 / 250000000000000000)) ^ 2 + 2 * ((2237666849 / 500000000000000000)) * ((358854493 / 1000000000000000000))) +
      6 * ((373261803 / 250000000000000000)) * ((358854493 / 1000000000000000000)) * (126 / 100) + 8 * ((358854493 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12821 163) (d.f1 12821 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12821 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12821 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12821 163) (d.f1 12821 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12821 163) (d.w1 12821 163) (d.w2 12821 163)
  have hwexpr0 : 0 ≤ d.w0 12821 163 + d.w1 12821 163 * √(π / 2) +
      2 * d.w2 12821 163 + energyR16 12821 *
      radiusPolynomialRoot16 (d.w0 12821 163) (d.w1 12821 163) (d.w2 12821 163) := by
    positivity
  constructor
  · change (12821 : ℝ) ^ 8 * (mA 12821 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12821 163) (d.f1 12821 163) d.f2 + locationR16 12821 *
        radiusPolynomialRoot16 (d.f0 12821 163) (d.f1 12821 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12821 : ℝ) ^ 8 * (mA 12821 : ℝ) ^ 8 *
        ((((2237666849 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2237666849 / 500000000000000000)) * ((373261803 / 250000000000000000)) * (126 / 100) +
          2 * (((373261803 / 250000000000000000)) ^ 2 + 2 * ((2237666849 / 500000000000000000)) * ((358854493 / 1000000000000000000))) +
          6 * ((373261803 / 250000000000000000)) * ((358854493 / 1000000000000000000)) * (126 / 100) + 8 * ((358854493 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12821) *
          (32 * (((2237666849 / 500000000000000000) : ℝ) + (373261803 / 250000000000000000) + (358854493 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12821 : ℝ) ^ 16 *
      (d.w0 12821 163 + d.w1 12821 163 * √(π / 2) + 2 * d.w2 12821 163 +
        energyR16 12821 * radiusPolynomialRoot16 (d.w0 12821 163) (d.w1 12821 163)
          (d.w2 12821 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12821 : ℝ) ^ 16 *
        (((1781781381 / 100000000000000000000) : ℝ) + ((633851739 / 50000000000000000000)) * (126 / 100) + 2 * ((231593401 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12821) *
          (32 * (((1781781381 / 100000000000000000000) : ℝ) + (633851739 / 50000000000000000000) + (231593401 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12821

/-! A coarse bound on the actual paper statistics constant at dimension 12822. -/
namespace BstLean.Part266.Row12822
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12820 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12820 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12820 128 ≤ (13074 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13074 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12822) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12822 : ℕ))
    (by norm_num : (12822 : ℕ) ≤ 16384)
  have ht : paperTail256 12822 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12822 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12822 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12822 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12822 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12822 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12820 128 * √(2 / (12822 : ℝ)) *
      (√(12822 : ℝ) + paperT0 12822 + paperTail256 12822) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12822 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12822 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12822 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12820 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12820 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12822 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12822

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12822
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12822 (61 / 100) 163 (17 / (100 * 12822)) (26 / (10 * 12822)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12822 (61 / 100) 163 (17 / (100 * 12822)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (5788423 / 1250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (722311413 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4737153069 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12822 / 12822 * (61 / 100)) ^ 4 * inverseRadius8 (12822 - 1) /
            envelopeGap 12822 (61 / 100) 163 (17 / (100 * 12822)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12822

namespace BstLean.Part266.Row12822
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12822 163 ≤ (4474461107 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12822 163 ≤ (14927561 / 10000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (89696131 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12822 163 ≤ (890682251 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12822 163 ≤ (316851719 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12822 163 ≤ (463078429 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (5788423 / 1250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (5788423 / 1250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (722311413 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4737153069 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3641217 / 1000000000) : ℝ) ≤ √(17 / (100 * 12822) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12822) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (430383011 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9502048549 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12822) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12822) ≤ (13786983 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12822) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12822 * (163 : ℝ) ^ 2 + 26 / (10 * 12822) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12822) : ℝ)) (tA 12822 * 163 ^ 2 + 26 / (10 * 12822)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3641217 / 1000000000))) * ((5788423 / 1250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3641217 / 1000000000)) ^ 3) * ((722311413 / 500000000000000000000000))) + ((4737153069 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3641217 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12822) : ℝ)) d.D d.V d.P (√(tA 12822) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3641217 / 1000000000)) ^ 2 * (((430383011 / 200000000000000)) * ((9502048549 / 250000000000000000)))) + ((4737153069 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12822) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3641217 / 1000000000)) * ((5788423 / 1250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12822) : ℝ)) (tA 12822 * 163 ^ 2 + 26 / (10 * 12822)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((5788423 / 1250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3641217 / 1000000000)) ^ 2) * ((722311413 / 500000000000000000000000)) + ((4737153069 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12822) : ℝ)) (√(26 / (10 * 12822) : ℝ)) d.D d.V d.P (√(tA 12822) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3641217 / 1000000000)) * (((430383011 / 200000000000000)) * ((9502048549 / 250000000000000000))) + ((4737153069 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12822) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((5788423 / 1250000000000000000) : ℝ) + ((4737153069 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12822

namespace BstLean.Part266.Row12822
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12822 163 ∧
    0 ≤ (tableEnvelope C).f1 12822 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12822 163 ∧
    0 ≤ (tableEnvelope C).w1 12822 163 ∧ 0 ≤ (tableEnvelope C).w2 12822 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12822 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12822 163 ∧ 0 ≤ d.f1 12822 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12822 163 ∧ 0 ≤ d.w1 12822 163 ∧ 0 ≤ d.w2 12822 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12822 ≤ 2 * (228 / 100 : ℝ) / 12822 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12822 ≤ 2 * (370 / 100 : ℝ) / 12822 := by
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
    (completeRAData (tableEnvelope C) 12822 163).locationBound 12822 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12822 163).energyBound 12822 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12822 163) (d.f1 12822 163) d.f2 ≤
      32 * (((4474461107 / 1000000000000000000) : ℝ) + (14927561 / 10000000000000000) + (89696131 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12822 163) (d.w1 12822 163)
      (d.w2 12822 163) ≤
      32 * (((890682251 / 50000000000000000000) : ℝ) + (316851719 / 25000000000000000000) + (463078429 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12822 163) (d.f1 12822 163) d.f2 ≤
      ((4474461107 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4474461107 / 1000000000000000000)) * ((14927561 / 10000000000000000)) * (126 / 100) +
      2 * (((14927561 / 10000000000000000)) ^ 2 + 2 * ((4474461107 / 1000000000000000000)) * ((89696131 / 250000000000000000))) +
      6 * ((14927561 / 10000000000000000)) * ((89696131 / 250000000000000000)) * (126 / 100) + 8 * ((89696131 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12822 163) (d.f1 12822 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12822 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12822 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12822 163) (d.f1 12822 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12822 163) (d.w1 12822 163) (d.w2 12822 163)
  have hwexpr0 : 0 ≤ d.w0 12822 163 + d.w1 12822 163 * √(π / 2) +
      2 * d.w2 12822 163 + energyR16 12822 *
      radiusPolynomialRoot16 (d.w0 12822 163) (d.w1 12822 163) (d.w2 12822 163) := by
    positivity
  constructor
  · change (12822 : ℝ) ^ 8 * (mA 12822 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12822 163) (d.f1 12822 163) d.f2 + locationR16 12822 *
        radiusPolynomialRoot16 (d.f0 12822 163) (d.f1 12822 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12822 : ℝ) ^ 8 * (mA 12822 : ℝ) ^ 8 *
        ((((4474461107 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4474461107 / 1000000000000000000)) * ((14927561 / 10000000000000000)) * (126 / 100) +
          2 * (((14927561 / 10000000000000000)) ^ 2 + 2 * ((4474461107 / 1000000000000000000)) * ((89696131 / 250000000000000000))) +
          6 * ((14927561 / 10000000000000000)) * ((89696131 / 250000000000000000)) * (126 / 100) + 8 * ((89696131 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12822) *
          (32 * (((4474461107 / 1000000000000000000) : ℝ) + (14927561 / 10000000000000000) + (89696131 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12822 : ℝ) ^ 16 *
      (d.w0 12822 163 + d.w1 12822 163 * √(π / 2) + 2 * d.w2 12822 163 +
        energyR16 12822 * radiusPolynomialRoot16 (d.w0 12822 163) (d.w1 12822 163)
          (d.w2 12822 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12822 : ℝ) ^ 16 *
        (((890682251 / 50000000000000000000) : ℝ) + ((316851719 / 25000000000000000000)) * (126 / 100) + 2 * ((463078429 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12822) *
          (32 * (((890682251 / 50000000000000000000) : ℝ) + (316851719 / 25000000000000000000) + (463078429 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12822

/-! A coarse bound on the actual paper statistics constant at dimension 12823. -/
namespace BstLean.Part266.Row12823
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12821 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12821 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12821 128 ≤ (13075 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13075 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12823) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12823 : ℕ))
    (by norm_num : (12823 : ℕ) ≤ 16384)
  have ht : paperTail256 12823 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12823 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12823 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12823 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12823 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12823 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12821 128 * √(2 / (12823 : ℝ)) *
      (√(12823 : ℝ) + paperT0 12823 + paperTail256 12823) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12823 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12823 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12823 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12821 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12821 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12823 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12823

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12823
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12823 (61 / 100) 163 (17 / (100 * 12823)) (26 / (10 * 12823)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12823 (61 / 100) 163 (17 / (100 * 12823)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (92593101 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (722086113 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4734170237 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12823 / 12823 * (61 / 100)) ^ 4 * inverseRadius8 (12823 - 1) /
            envelopeGap 12823 (61 / 100) 163 (17 / (100 * 12823)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12823

namespace BstLean.Part266.Row12823
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12823 163 ≤ (4473588813 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12823 163 ≤ (746232541 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (22419661 / 62500000000000000)
  w0 : (tableEnvelope C).w0 12823 163 ≤ (1780947767 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12823 163 ≤ (633555187 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12823 163 ≤ (462970091 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (92593101 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (92593101 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (722086113 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4734170237 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((145643 / 40000000) : ℝ) ≤ √(17 / (100 * 12823) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12823) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1075831661 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7600453213 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12823) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12823) ≤ (110287263 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12823) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12823 * (163 : ℝ) ^ 2 + 26 / (10 * 12823) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12823) : ℝ)) (tA 12823 * 163 ^ 2 + 26 / (10 * 12823)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((145643 / 40000000))) * ((92593101 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((145643 / 40000000)) ^ 3) * ((722086113 / 500000000000000000000000))) + ((4734170237 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((145643 / 40000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12823) : ℝ)) d.D d.V d.P (√(tA 12823) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((145643 / 40000000)) ^ 2 * (((1075831661 / 500000000000000)) * ((7600453213 / 200000000000000000)))) + ((4734170237 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12823) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((145643 / 40000000)) * ((92593101 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12823) : ℝ)) (tA 12823 * 163 ^ 2 + 26 / (10 * 12823)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((92593101 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((145643 / 40000000)) ^ 2) * ((722086113 / 500000000000000000000000)) + ((4734170237 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12823) : ℝ)) (√(26 / (10 * 12823) : ℝ)) d.D d.V d.P (√(tA 12823) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((145643 / 40000000)) * (((1075831661 / 500000000000000)) * ((7600453213 / 200000000000000000))) + ((4734170237 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12823) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((92593101 / 20000000000000000000) : ℝ) + ((4734170237 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12823

namespace BstLean.Part266.Row12823
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12823 163 ∧
    0 ≤ (tableEnvelope C).f1 12823 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12823 163 ∧
    0 ≤ (tableEnvelope C).w1 12823 163 ∧ 0 ≤ (tableEnvelope C).w2 12823 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12823 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12823 163 ∧ 0 ≤ d.f1 12823 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12823 163 ∧ 0 ≤ d.w1 12823 163 ∧ 0 ≤ d.w2 12823 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12823 ≤ 2 * (228 / 100 : ℝ) / 12823 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12823 ≤ 2 * (370 / 100 : ℝ) / 12823 := by
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
    (completeRAData (tableEnvelope C) 12823 163).locationBound 12823 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12823 163).energyBound 12823 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12823 163) (d.f1 12823 163) d.f2 ≤
      32 * (((4473588813 / 1000000000000000000) : ℝ) + (746232541 / 500000000000000000) + (22419661 / 62500000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12823 163) (d.w1 12823 163)
      (d.w2 12823 163) ≤
      32 * (((1780947767 / 100000000000000000000) : ℝ) + (633555187 / 50000000000000000000) + (462970091 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12823 163) (d.f1 12823 163) d.f2 ≤
      ((4473588813 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4473588813 / 1000000000000000000)) * ((746232541 / 500000000000000000)) * (126 / 100) +
      2 * (((746232541 / 500000000000000000)) ^ 2 + 2 * ((4473588813 / 1000000000000000000)) * ((22419661 / 62500000000000000))) +
      6 * ((746232541 / 500000000000000000)) * ((22419661 / 62500000000000000)) * (126 / 100) + 8 * ((22419661 / 62500000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12823 163) (d.f1 12823 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12823 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12823 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12823 163) (d.f1 12823 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12823 163) (d.w1 12823 163) (d.w2 12823 163)
  have hwexpr0 : 0 ≤ d.w0 12823 163 + d.w1 12823 163 * √(π / 2) +
      2 * d.w2 12823 163 + energyR16 12823 *
      radiusPolynomialRoot16 (d.w0 12823 163) (d.w1 12823 163) (d.w2 12823 163) := by
    positivity
  constructor
  · change (12823 : ℝ) ^ 8 * (mA 12823 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12823 163) (d.f1 12823 163) d.f2 + locationR16 12823 *
        radiusPolynomialRoot16 (d.f0 12823 163) (d.f1 12823 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12823 : ℝ) ^ 8 * (mA 12823 : ℝ) ^ 8 *
        ((((4473588813 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4473588813 / 1000000000000000000)) * ((746232541 / 500000000000000000)) * (126 / 100) +
          2 * (((746232541 / 500000000000000000)) ^ 2 + 2 * ((4473588813 / 1000000000000000000)) * ((22419661 / 62500000000000000))) +
          6 * ((746232541 / 500000000000000000)) * ((22419661 / 62500000000000000)) * (126 / 100) + 8 * ((22419661 / 62500000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12823) *
          (32 * (((4473588813 / 1000000000000000000) : ℝ) + (746232541 / 500000000000000000) + (22419661 / 62500000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12823 : ℝ) ^ 16 *
      (d.w0 12823 163 + d.w1 12823 163 * √(π / 2) + 2 * d.w2 12823 163 +
        energyR16 12823 * radiusPolynomialRoot16 (d.w0 12823 163) (d.w1 12823 163)
          (d.w2 12823 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12823 : ℝ) ^ 16 *
        (((1780947767 / 100000000000000000000) : ℝ) + ((633555187 / 50000000000000000000)) * (126 / 100) + 2 * ((462970091 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12823) *
          (32 * (((1780947767 / 100000000000000000000) : ℝ) + (633555187 / 50000000000000000000) + (462970091 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12823

/-! A coarse bound on the actual paper statistics constant at dimension 12824. -/
namespace BstLean.Part266.Row12824
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12822 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12822 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12822 128 ≤ (13076 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13076 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12824) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12824 : ℕ))
    (by norm_num : (12824 : ℕ) ≤ 16384)
  have ht : paperTail256 12824 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12824 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12824 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12824 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12824 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12824 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12822 128 * √(2 / (12824 : ℝ)) *
      (√(12824 : ℝ) + paperT0 12824 + paperTail256 12824) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12824 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12824 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12824 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12822 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12822 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12824 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12824

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12824
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12824 (61 / 100) 163 (17 / (100 * 12824)) (26 / (10 * 12824)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12824 (61 / 100) 163 (17 / (100 * 12824)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (462857203 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (721860901 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (59139869 / 12500000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12824 / 12824 * (61 / 100)) ^ 4 * inverseRadius8 (12824 - 1) /
            envelopeGap 12824 (61 / 100) 163 (17 / (100 * 12824)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12824

namespace BstLean.Part266.Row12824
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12824 163 ≤ (2236358409 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12824 163 ≤ (373043539 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (358644649 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12824 163 ≤ (1780531173 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12824 163 ≤ (126681397 / 10000000000000000000)
  w2 : (tableEnvelope C).w2 12824 163 ≤ (462861787 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (462857203 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (462857203 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (721860901 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (59139869 / 12500000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3640933 / 1000000000) : ℝ) ≤ √(17 / (100 * 12824) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12824) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2151411637 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9499084831 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12824) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12824) ≤ (110278663 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12824) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12824 * (163 : ℝ) ^ 2 + 26 / (10 * 12824) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12824) : ℝ)) (tA 12824 * 163 ^ 2 + 26 / (10 * 12824)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3640933 / 1000000000))) * ((462857203 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3640933 / 1000000000)) ^ 3) * ((721860901 / 500000000000000000000000))) + ((59139869 / 12500000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3640933 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12824) : ℝ)) d.D d.V d.P (√(tA 12824) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3640933 / 1000000000)) ^ 2 * (((2151411637 / 1000000000000000)) * ((9499084831 / 250000000000000000)))) + ((59139869 / 12500000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12824) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3640933 / 1000000000)) * ((462857203 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12824) : ℝ)) (tA 12824 * 163 ^ 2 + 26 / (10 * 12824)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((462857203 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3640933 / 1000000000)) ^ 2) * ((721860901 / 500000000000000000000000)) + ((59139869 / 12500000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12824) : ℝ)) (√(26 / (10 * 12824) : ℝ)) d.D d.V d.P (√(tA 12824) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3640933 / 1000000000)) * (((2151411637 / 1000000000000000)) * ((9499084831 / 250000000000000000))) + ((59139869 / 12500000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12824) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((462857203 / 100000000000000000000) : ℝ) + ((59139869 / 12500000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12824

namespace BstLean.Part266.Row12824
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12824 163 ∧
    0 ≤ (tableEnvelope C).f1 12824 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12824 163 ∧
    0 ≤ (tableEnvelope C).w1 12824 163 ∧ 0 ≤ (tableEnvelope C).w2 12824 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12824 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12824 163 ∧ 0 ≤ d.f1 12824 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12824 163 ∧ 0 ≤ d.w1 12824 163 ∧ 0 ≤ d.w2 12824 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12824 ≤ 2 * (228 / 100 : ℝ) / 12824 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12824 ≤ 2 * (370 / 100 : ℝ) / 12824 := by
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
    (completeRAData (tableEnvelope C) 12824 163).locationBound 12824 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12824 163).energyBound 12824 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12824 163) (d.f1 12824 163) d.f2 ≤
      32 * (((2236358409 / 500000000000000000) : ℝ) + (373043539 / 250000000000000000) + (358644649 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12824 163) (d.w1 12824 163)
      (d.w2 12824 163) ≤
      32 * (((1780531173 / 100000000000000000000) : ℝ) + (126681397 / 10000000000000000000) + (462861787 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12824 163) (d.f1 12824 163) d.f2 ≤
      ((2236358409 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2236358409 / 500000000000000000)) * ((373043539 / 250000000000000000)) * (126 / 100) +
      2 * (((373043539 / 250000000000000000)) ^ 2 + 2 * ((2236358409 / 500000000000000000)) * ((358644649 / 1000000000000000000))) +
      6 * ((373043539 / 250000000000000000)) * ((358644649 / 1000000000000000000)) * (126 / 100) + 8 * ((358644649 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12824 163) (d.f1 12824 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12824 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12824 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12824 163) (d.f1 12824 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12824 163) (d.w1 12824 163) (d.w2 12824 163)
  have hwexpr0 : 0 ≤ d.w0 12824 163 + d.w1 12824 163 * √(π / 2) +
      2 * d.w2 12824 163 + energyR16 12824 *
      radiusPolynomialRoot16 (d.w0 12824 163) (d.w1 12824 163) (d.w2 12824 163) := by
    positivity
  constructor
  · change (12824 : ℝ) ^ 8 * (mA 12824 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12824 163) (d.f1 12824 163) d.f2 + locationR16 12824 *
        radiusPolynomialRoot16 (d.f0 12824 163) (d.f1 12824 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12824 : ℝ) ^ 8 * (mA 12824 : ℝ) ^ 8 *
        ((((2236358409 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2236358409 / 500000000000000000)) * ((373043539 / 250000000000000000)) * (126 / 100) +
          2 * (((373043539 / 250000000000000000)) ^ 2 + 2 * ((2236358409 / 500000000000000000)) * ((358644649 / 1000000000000000000))) +
          6 * ((373043539 / 250000000000000000)) * ((358644649 / 1000000000000000000)) * (126 / 100) + 8 * ((358644649 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12824) *
          (32 * (((2236358409 / 500000000000000000) : ℝ) + (373043539 / 250000000000000000) + (358644649 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12824 : ℝ) ^ 16 *
      (d.w0 12824 163 + d.w1 12824 163 * √(π / 2) + 2 * d.w2 12824 163 +
        energyR16 12824 * radiusPolynomialRoot16 (d.w0 12824 163) (d.w1 12824 163)
          (d.w2 12824 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12824 : ℝ) ^ 16 *
        (((1780531173 / 100000000000000000000) : ℝ) + ((126681397 / 10000000000000000000)) * (126 / 100) + 2 * ((462861787 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12824) *
          (32 * (((1780531173 / 100000000000000000000) : ℝ) + (126681397 / 10000000000000000000) + (462861787 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12824
