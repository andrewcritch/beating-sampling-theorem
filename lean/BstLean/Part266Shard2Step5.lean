import BstLean.Part266Shard2Step4


/-! A coarse bound on the actual paper statistics constant at dimension 12400. -/
namespace BstLean.Part266.Row12400
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12398 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12398 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12398 128 ≤ (12652 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12652 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12400) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12400 : ℕ))
    (by norm_num : (12400 : ℕ) ≤ 16384)
  have ht : paperTail256 12400 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12400 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12400 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12400 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12400 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12400 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12398 128 * √(2 / (12400 : ℝ)) *
      (√(12400 : ℝ) + paperT0 12400 + paperTail256 12400) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12400 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12400 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12400 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12398 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12398 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12400 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12400

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12400
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12400 (61 / 100) 161 (17 / (100 * 12400)) (26 / (10 * 12400)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12400 (61 / 100) 161 (17 / (100 * 12400)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (102396429 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (412888833 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6201785147 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12400 / 12400 * (61 / 100)) ^ 4 * inverseRadius8 (12400 - 1) /
            envelopeGap 12400 (61 / 100) 161 (17 / (100 * 12400)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12400

namespace BstLean.Part266.Row12400
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12400 161 ≤ (4864948933 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12400 161 ≤ (1623029523 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (390095761 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12400 161 ≤ (1969506497 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12400 161 ≤ (1401266303 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12400 161 ≤ (511988153 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (102396429 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (102396429 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (412888833 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6201785147 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1851329 / 500000000) : ℝ) ≤ √(17 / (100 * 12400) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12400) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1131351123 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (5079916541 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12400) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12400) ≤ (114049481 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12400) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12400 * (161 : ℝ) ^ 2 + 26 / (10 * 12400) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12400) : ℝ)) (tA 12400 * 161 ^ 2 + 26 / (10 * 12400)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1851329 / 500000000))) * ((102396429 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1851329 / 500000000)) ^ 3) * ((412888833 / 250000000000000000000000))) + ((6201785147 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1851329 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12400) : ℝ)) d.D d.V d.P (√(tA 12400) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1851329 / 500000000)) ^ 2 * (((1131351123 / 500000000000000)) * ((5079916541 / 125000000000000000)))) + ((6201785147 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12400) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1851329 / 500000000)) * ((102396429 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12400) : ℝ)) (tA 12400 * 161 ^ 2 + 26 / (10 * 12400)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((102396429 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1851329 / 500000000)) ^ 2) * ((412888833 / 250000000000000000000000)) + ((6201785147 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12400) : ℝ)) (√(26 / (10 * 12400) : ℝ)) d.D d.V d.P (√(tA 12400) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1851329 / 500000000)) * (((1131351123 / 500000000000000)) * ((5079916541 / 125000000000000000))) + ((6201785147 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12400) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((102396429 / 20000000000000000000) : ℝ) + ((6201785147 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12400

namespace BstLean.Part266.Row12400
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12400 161 ∧
    0 ≤ (tableEnvelope C).f1 12400 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12400 161 ∧
    0 ≤ (tableEnvelope C).w1 12400 161 ∧ 0 ≤ (tableEnvelope C).w2 12400 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12400 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12400 161 ∧ 0 ≤ d.f1 12400 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12400 161 ∧ 0 ≤ d.w1 12400 161 ∧ 0 ≤ d.w2 12400 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12400 ≤ 2 * (228 / 100 : ℝ) / 12400 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12400 ≤ 2 * (370 / 100 : ℝ) / 12400 := by
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
    (completeRAData (tableEnvelope C) 12400 161).locationBound 12400 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12400 161).energyBound 12400 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12400 161) (d.f1 12400 161) d.f2 ≤
      32 * (((4864948933 / 1000000000000000000) : ℝ) + (1623029523 / 1000000000000000000) + (390095761 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12400 161) (d.w1 12400 161)
      (d.w2 12400 161) ≤
      32 * (((1969506497 / 100000000000000000000) : ℝ) + (1401266303 / 100000000000000000000) + (511988153 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12400 161) (d.f1 12400 161) d.f2 ≤
      ((4864948933 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4864948933 / 1000000000000000000)) * ((1623029523 / 1000000000000000000)) * (126 / 100) +
      2 * (((1623029523 / 1000000000000000000)) ^ 2 + 2 * ((4864948933 / 1000000000000000000)) * ((390095761 / 1000000000000000000))) +
      6 * ((1623029523 / 1000000000000000000)) * ((390095761 / 1000000000000000000)) * (126 / 100) + 8 * ((390095761 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12400 161) (d.f1 12400 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12400 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12400 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12400 161) (d.f1 12400 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12400 161) (d.w1 12400 161) (d.w2 12400 161)
  have hwexpr0 : 0 ≤ d.w0 12400 161 + d.w1 12400 161 * √(π / 2) +
      2 * d.w2 12400 161 + energyR16 12400 *
      radiusPolynomialRoot16 (d.w0 12400 161) (d.w1 12400 161) (d.w2 12400 161) := by
    positivity
  constructor
  · change (12400 : ℝ) ^ 8 * (mA 12400 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12400 161) (d.f1 12400 161) d.f2 + locationR16 12400 *
        radiusPolynomialRoot16 (d.f0 12400 161) (d.f1 12400 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12400 : ℝ) ^ 8 * (mA 12400 : ℝ) ^ 8 *
        ((((4864948933 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4864948933 / 1000000000000000000)) * ((1623029523 / 1000000000000000000)) * (126 / 100) +
          2 * (((1623029523 / 1000000000000000000)) ^ 2 + 2 * ((4864948933 / 1000000000000000000)) * ((390095761 / 1000000000000000000))) +
          6 * ((1623029523 / 1000000000000000000)) * ((390095761 / 1000000000000000000)) * (126 / 100) + 8 * ((390095761 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12400) *
          (32 * (((4864948933 / 1000000000000000000) : ℝ) + (1623029523 / 1000000000000000000) + (390095761 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12400 : ℝ) ^ 16 *
      (d.w0 12400 161 + d.w1 12400 161 * √(π / 2) + 2 * d.w2 12400 161 +
        energyR16 12400 * radiusPolynomialRoot16 (d.w0 12400 161) (d.w1 12400 161)
          (d.w2 12400 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12400 : ℝ) ^ 16 *
        (((1969506497 / 100000000000000000000) : ℝ) + ((1401266303 / 100000000000000000000)) * (126 / 100) + 2 * ((511988153 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12400) *
          (32 * (((1969506497 / 100000000000000000000) : ℝ) + (1401266303 / 100000000000000000000) + (511988153 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12400

/-! A coarse bound on the actual paper statistics constant at dimension 12401. -/
namespace BstLean.Part266.Row12401
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12399 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12399 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12399 128 ≤ (12653 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12653 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12401) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12401 : ℕ))
    (by norm_num : (12401 : ℕ) ≤ 16384)
  have ht : paperTail256 12401 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12401 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12401 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12401 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12401 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12401 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12399 128 * √(2 / (12401 : ℝ)) *
      (√(12401 : ℝ) + paperT0 12401 + paperTail256 12401) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12401 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12401 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12401 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12399 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12399 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12401 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12401

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12401
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12401 (61 / 100) 161 (17 / (100 * 12401)) (26 / (10 * 12401)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12401 (61 / 100) 161 (17 / (100 * 12401)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (127964573 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (825511329 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3098872793 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12401 / 12401 * (61 / 100)) ^ 4 * inverseRadius8 (12401 - 1) /
            envelopeGap 12401 (61 / 100) 161 (17 / (100 * 12401)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12401

namespace BstLean.Part266.Row12401
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12401 161 ≤ (4863970857 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12401 161 ≤ (324540589 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (195008597 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12401 161 ≤ (492257653 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12401 161 ≤ (175115949 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 12401 161 ≤ (63983037 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (127964573 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (127964573 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (825511329 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3098872793 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((925627 / 250000000) : ℝ) ≤ √(17 / (100 * 12401) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12401) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (452485709 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (10158194531 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12401) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12401) ≤ (22808057 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12401) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12401 * (161 : ℝ) ^ 2 + 26 / (10 * 12401) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12401) : ℝ)) (tA 12401 * 161 ^ 2 + 26 / (10 * 12401)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((925627 / 250000000))) * ((127964573 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((925627 / 250000000)) ^ 3) * ((825511329 / 500000000000000000000000))) + ((3098872793 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((925627 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12401) : ℝ)) d.D d.V d.P (√(tA 12401) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((925627 / 250000000)) ^ 2 * (((452485709 / 200000000000000)) * ((10158194531 / 250000000000000000)))) + ((3098872793 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12401) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((925627 / 250000000)) * ((127964573 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12401) : ℝ)) (tA 12401 * 161 ^ 2 + 26 / (10 * 12401)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((127964573 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((925627 / 250000000)) ^ 2) * ((825511329 / 500000000000000000000000)) + ((3098872793 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12401) : ℝ)) (√(26 / (10 * 12401) : ℝ)) d.D d.V d.P (√(tA 12401) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((925627 / 250000000)) * (((452485709 / 200000000000000)) * ((10158194531 / 250000000000000000))) + ((3098872793 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12401) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((127964573 / 25000000000000000000) : ℝ) + ((3098872793 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12401

namespace BstLean.Part266.Row12401
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12401 161 ∧
    0 ≤ (tableEnvelope C).f1 12401 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12401 161 ∧
    0 ≤ (tableEnvelope C).w1 12401 161 ∧ 0 ≤ (tableEnvelope C).w2 12401 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12401 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12401 161 ∧ 0 ≤ d.f1 12401 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12401 161 ∧ 0 ≤ d.w1 12401 161 ∧ 0 ≤ d.w2 12401 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12401 ≤ 2 * (228 / 100 : ℝ) / 12401 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12401 ≤ 2 * (370 / 100 : ℝ) / 12401 := by
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
    (completeRAData (tableEnvelope C) 12401 161).locationBound 12401 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12401 161).energyBound 12401 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12401 161) (d.f1 12401 161) d.f2 ≤
      32 * (((4863970857 / 1000000000000000000) : ℝ) + (324540589 / 200000000000000000) + (195008597 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12401 161) (d.w1 12401 161)
      (d.w2 12401 161) ≤
      32 * (((492257653 / 25000000000000000000) : ℝ) + (175115949 / 12500000000000000000) + (63983037 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12401 161) (d.f1 12401 161) d.f2 ≤
      ((4863970857 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4863970857 / 1000000000000000000)) * ((324540589 / 200000000000000000)) * (126 / 100) +
      2 * (((324540589 / 200000000000000000)) ^ 2 + 2 * ((4863970857 / 1000000000000000000)) * ((195008597 / 500000000000000000))) +
      6 * ((324540589 / 200000000000000000)) * ((195008597 / 500000000000000000)) * (126 / 100) + 8 * ((195008597 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12401 161) (d.f1 12401 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12401 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12401 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12401 161) (d.f1 12401 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12401 161) (d.w1 12401 161) (d.w2 12401 161)
  have hwexpr0 : 0 ≤ d.w0 12401 161 + d.w1 12401 161 * √(π / 2) +
      2 * d.w2 12401 161 + energyR16 12401 *
      radiusPolynomialRoot16 (d.w0 12401 161) (d.w1 12401 161) (d.w2 12401 161) := by
    positivity
  constructor
  · change (12401 : ℝ) ^ 8 * (mA 12401 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12401 161) (d.f1 12401 161) d.f2 + locationR16 12401 *
        radiusPolynomialRoot16 (d.f0 12401 161) (d.f1 12401 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12401 : ℝ) ^ 8 * (mA 12401 : ℝ) ^ 8 *
        ((((4863970857 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4863970857 / 1000000000000000000)) * ((324540589 / 200000000000000000)) * (126 / 100) +
          2 * (((324540589 / 200000000000000000)) ^ 2 + 2 * ((4863970857 / 1000000000000000000)) * ((195008597 / 500000000000000000))) +
          6 * ((324540589 / 200000000000000000)) * ((195008597 / 500000000000000000)) * (126 / 100) + 8 * ((195008597 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12401) *
          (32 * (((4863970857 / 1000000000000000000) : ℝ) + (324540589 / 200000000000000000) + (195008597 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12401 : ℝ) ^ 16 *
      (d.w0 12401 161 + d.w1 12401 161 * √(π / 2) + 2 * d.w2 12401 161 +
        energyR16 12401 * radiusPolynomialRoot16 (d.w0 12401 161) (d.w1 12401 161)
          (d.w2 12401 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12401 : ℝ) ^ 16 *
        (((492257653 / 25000000000000000000) : ℝ) + ((175115949 / 12500000000000000000)) * (126 / 100) + 2 * ((63983037 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12401) *
          (32 * (((492257653 / 25000000000000000000) : ℝ) + (175115949 / 12500000000000000000) + (63983037 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12401

/-! A coarse bound on the actual paper statistics constant at dimension 12402. -/
namespace BstLean.Part266.Row12402
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12400 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12400 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12400 128 ≤ (12654 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12654 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12402) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12402 : ℕ))
    (by norm_num : (12402 : ℕ) ≤ 16384)
  have ht : paperTail256 12402 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12402 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12402 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12402 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12402 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12402 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12400 128 * √(2 / (12402 : ℝ)) *
      (√(12402 : ℝ) + paperT0 12402 + paperTail256 12402) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12402 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12402 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12402 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12400 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12400 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12402 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12402

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12402
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12402 (61 / 100) 161 (17 / (100 * 12402)) (26 / (10 * 12402)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12402 (61 / 100) 161 (17 / (100 * 12402)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (511734479 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1650490199 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1548427247 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12402 / 12402 * (61 / 100)) ^ 4 * inverseRadius8 (12402 - 1) /
            envelopeGap 12402 (61 / 100) 161 (17 / (100 * 12402)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12402

namespace BstLean.Part266.Row12402
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12402 161 ≤ (972597867 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12402 161 ≤ (1622375599 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (77987709 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12402 161 ≤ (492138527 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12402 161 ≤ (700294309 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12402 161 ≤ (511740479 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (511734479 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (511734479 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1650490199 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1548427247 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3702359 / 1000000000) : ℝ) ≤ √(17 / (100 * 12402) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12402) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (22621549 / 10000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (10156556377 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12402) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12402) ≤ (114031089 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12402) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12402 * (161 : ℝ) ^ 2 + 26 / (10 * 12402) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12402) : ℝ)) (tA 12402 * 161 ^ 2 + 26 / (10 * 12402)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3702359 / 1000000000))) * ((511734479 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3702359 / 1000000000)) ^ 3) * ((1650490199 / 1000000000000000000000000))) + ((1548427247 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3702359 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12402) : ℝ)) d.D d.V d.P (√(tA 12402) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3702359 / 1000000000)) ^ 2 * (((22621549 / 10000000000000)) * ((10156556377 / 250000000000000000)))) + ((1548427247 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12402) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3702359 / 1000000000)) * ((511734479 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12402) : ℝ)) (tA 12402 * 161 ^ 2 + 26 / (10 * 12402)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((511734479 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3702359 / 1000000000)) ^ 2) * ((1650490199 / 1000000000000000000000000)) + ((1548427247 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12402) : ℝ)) (√(26 / (10 * 12402) : ℝ)) d.D d.V d.P (√(tA 12402) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3702359 / 1000000000)) * (((22621549 / 10000000000000)) * ((10156556377 / 250000000000000000))) + ((1548427247 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12402) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((511734479 / 100000000000000000000) : ℝ) + ((1548427247 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12402

namespace BstLean.Part266.Row12402
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12402 161 ∧
    0 ≤ (tableEnvelope C).f1 12402 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12402 161 ∧
    0 ≤ (tableEnvelope C).w1 12402 161 ∧ 0 ≤ (tableEnvelope C).w2 12402 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12402 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12402 161 ∧ 0 ≤ d.f1 12402 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12402 161 ∧ 0 ≤ d.w1 12402 161 ∧ 0 ≤ d.w2 12402 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12402 ≤ 2 * (228 / 100 : ℝ) / 12402 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12402 ≤ 2 * (370 / 100 : ℝ) / 12402 := by
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
    (completeRAData (tableEnvelope C) 12402 161).locationBound 12402 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12402 161).energyBound 12402 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12402 161) (d.f1 12402 161) d.f2 ≤
      32 * (((972597867 / 200000000000000000) : ℝ) + (1622375599 / 1000000000000000000) + (77987709 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12402 161) (d.w1 12402 161)
      (d.w2 12402 161) ≤
      32 * (((492138527 / 25000000000000000000) : ℝ) + (700294309 / 50000000000000000000) + (511740479 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12402 161) (d.f1 12402 161) d.f2 ≤
      ((972597867 / 200000000000000000) : ℝ) ^ 2 + 2 * ((972597867 / 200000000000000000)) * ((1622375599 / 1000000000000000000)) * (126 / 100) +
      2 * (((1622375599 / 1000000000000000000)) ^ 2 + 2 * ((972597867 / 200000000000000000)) * ((77987709 / 200000000000000000))) +
      6 * ((1622375599 / 1000000000000000000)) * ((77987709 / 200000000000000000)) * (126 / 100) + 8 * ((77987709 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12402 161) (d.f1 12402 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12402 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12402 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12402 161) (d.f1 12402 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12402 161) (d.w1 12402 161) (d.w2 12402 161)
  have hwexpr0 : 0 ≤ d.w0 12402 161 + d.w1 12402 161 * √(π / 2) +
      2 * d.w2 12402 161 + energyR16 12402 *
      radiusPolynomialRoot16 (d.w0 12402 161) (d.w1 12402 161) (d.w2 12402 161) := by
    positivity
  constructor
  · change (12402 : ℝ) ^ 8 * (mA 12402 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12402 161) (d.f1 12402 161) d.f2 + locationR16 12402 *
        radiusPolynomialRoot16 (d.f0 12402 161) (d.f1 12402 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12402 : ℝ) ^ 8 * (mA 12402 : ℝ) ^ 8 *
        ((((972597867 / 200000000000000000) : ℝ) ^ 2 + 2 * ((972597867 / 200000000000000000)) * ((1622375599 / 1000000000000000000)) * (126 / 100) +
          2 * (((1622375599 / 1000000000000000000)) ^ 2 + 2 * ((972597867 / 200000000000000000)) * ((77987709 / 200000000000000000))) +
          6 * ((1622375599 / 1000000000000000000)) * ((77987709 / 200000000000000000)) * (126 / 100) + 8 * ((77987709 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12402) *
          (32 * (((972597867 / 200000000000000000) : ℝ) + (1622375599 / 1000000000000000000) + (77987709 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12402 : ℝ) ^ 16 *
      (d.w0 12402 161 + d.w1 12402 161 * √(π / 2) + 2 * d.w2 12402 161 +
        energyR16 12402 * radiusPolynomialRoot16 (d.w0 12402 161) (d.w1 12402 161)
          (d.w2 12402 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12402 : ℝ) ^ 16 *
        (((492138527 / 25000000000000000000) : ℝ) + ((700294309 / 50000000000000000000)) * (126 / 100) + 2 * ((511740479 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12402) *
          (32 * (((492138527 / 25000000000000000000) : ℝ) + (700294309 / 50000000000000000000) + (511740479 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12402

/-! A coarse bound on the actual paper statistics constant at dimension 12403. -/
namespace BstLean.Part266.Row12403
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12401 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12401 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12401 128 ≤ (12655 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12655 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12403) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12403 : ℕ))
    (by norm_num : (12403 : ℕ) ≤ 16384)
  have ht : paperTail256 12403 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12403 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12403 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12403 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12403 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12403 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12401 128 * √(2 / (12403 : ℝ)) *
      (√(12403 : ℝ) + paperT0 12403 + paperTail256 12403) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12403 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12403 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12403 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12401 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12401 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12403 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12403

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12403
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12403 (61 / 100) 161 (17 / (100 * 12403)) (26 / (10 * 12403)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12403 (61 / 100) 161 (17 / (100 * 12403)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (102322141 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (329991591 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6189675351 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12403 / 12403 * (61 / 100)) ^ 4 * inverseRadius8 (12403 - 1) /
            envelopeGap 12403 (61 / 100) 161 (17 / (100 * 12403)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12403

namespace BstLean.Part266.Row12403
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12403 161 ≤ (4862008159 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12403 161 ≤ (40551209 / 25000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (4873249 / 12500000000000000)
  w0 : (tableEnvelope C).w0 12403 161 ≤ (1968077771 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12403 161 ≤ (1400249759 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12403 161 ≤ (511616701 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (102322141 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (102322141 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (329991591 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6189675351 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((370221 / 100000000) : ℝ) ≤ √(17 / (100 * 12403) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12403) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (565470327 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (20309837241 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12403) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12403) ≤ (22804379 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12403) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12403 * (161 : ℝ) ^ 2 + 26 / (10 * 12403) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12403) : ℝ)) (tA 12403 * 161 ^ 2 + 26 / (10 * 12403)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((370221 / 100000000))) * ((102322141 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((370221 / 100000000)) ^ 3) * ((329991591 / 200000000000000000000000))) + ((6189675351 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((370221 / 100000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12403) : ℝ)) d.D d.V d.P (√(tA 12403) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((370221 / 100000000)) ^ 2 * (((565470327 / 250000000000000)) * ((20309837241 / 500000000000000000)))) + ((6189675351 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12403) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((370221 / 100000000)) * ((102322141 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12403) : ℝ)) (tA 12403 * 161 ^ 2 + 26 / (10 * 12403)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((102322141 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((370221 / 100000000)) ^ 2) * ((329991591 / 200000000000000000000000)) + ((6189675351 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12403) : ℝ)) (√(26 / (10 * 12403) : ℝ)) d.D d.V d.P (√(tA 12403) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((370221 / 100000000)) * (((565470327 / 250000000000000)) * ((20309837241 / 500000000000000000))) + ((6189675351 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12403) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((102322141 / 20000000000000000000) : ℝ) + ((6189675351 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12403

namespace BstLean.Part266.Row12403
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12403 161 ∧
    0 ≤ (tableEnvelope C).f1 12403 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12403 161 ∧
    0 ≤ (tableEnvelope C).w1 12403 161 ∧ 0 ≤ (tableEnvelope C).w2 12403 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12403 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12403 161 ∧ 0 ≤ d.f1 12403 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12403 161 ∧ 0 ≤ d.w1 12403 161 ∧ 0 ≤ d.w2 12403 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12403 ≤ 2 * (228 / 100 : ℝ) / 12403 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12403 ≤ 2 * (370 / 100 : ℝ) / 12403 := by
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
    (completeRAData (tableEnvelope C) 12403 161).locationBound 12403 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12403 161).energyBound 12403 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12403 161) (d.f1 12403 161) d.f2 ≤
      32 * (((4862008159 / 1000000000000000000) : ℝ) + (40551209 / 25000000000000000) + (4873249 / 12500000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12403 161) (d.w1 12403 161)
      (d.w2 12403 161) ≤
      32 * (((1968077771 / 100000000000000000000) : ℝ) + (1400249759 / 100000000000000000000) + (511616701 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12403 161) (d.f1 12403 161) d.f2 ≤
      ((4862008159 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4862008159 / 1000000000000000000)) * ((40551209 / 25000000000000000)) * (126 / 100) +
      2 * (((40551209 / 25000000000000000)) ^ 2 + 2 * ((4862008159 / 1000000000000000000)) * ((4873249 / 12500000000000000))) +
      6 * ((40551209 / 25000000000000000)) * ((4873249 / 12500000000000000)) * (126 / 100) + 8 * ((4873249 / 12500000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12403 161) (d.f1 12403 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12403 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12403 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12403 161) (d.f1 12403 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12403 161) (d.w1 12403 161) (d.w2 12403 161)
  have hwexpr0 : 0 ≤ d.w0 12403 161 + d.w1 12403 161 * √(π / 2) +
      2 * d.w2 12403 161 + energyR16 12403 *
      radiusPolynomialRoot16 (d.w0 12403 161) (d.w1 12403 161) (d.w2 12403 161) := by
    positivity
  constructor
  · change (12403 : ℝ) ^ 8 * (mA 12403 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12403 161) (d.f1 12403 161) d.f2 + locationR16 12403 *
        radiusPolynomialRoot16 (d.f0 12403 161) (d.f1 12403 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12403 : ℝ) ^ 8 * (mA 12403 : ℝ) ^ 8 *
        ((((4862008159 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4862008159 / 1000000000000000000)) * ((40551209 / 25000000000000000)) * (126 / 100) +
          2 * (((40551209 / 25000000000000000)) ^ 2 + 2 * ((4862008159 / 1000000000000000000)) * ((4873249 / 12500000000000000))) +
          6 * ((40551209 / 25000000000000000)) * ((4873249 / 12500000000000000)) * (126 / 100) + 8 * ((4873249 / 12500000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12403) *
          (32 * (((4862008159 / 1000000000000000000) : ℝ) + (40551209 / 25000000000000000) + (4873249 / 12500000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12403 : ℝ) ^ 16 *
      (d.w0 12403 161 + d.w1 12403 161 * √(π / 2) + 2 * d.w2 12403 161 +
        energyR16 12403 * radiusPolynomialRoot16 (d.w0 12403 161) (d.w1 12403 161)
          (d.w2 12403 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12403 : ℝ) ^ 16 *
        (((1968077771 / 100000000000000000000) : ℝ) + ((1400249759 / 100000000000000000000)) * (126 / 100) + 2 * ((511616701 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12403) *
          (32 * (((1968077771 / 100000000000000000000) : ℝ) + (1400249759 / 100000000000000000000) + (511616701 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12403

/-! A coarse bound on the actual paper statistics constant at dimension 12404. -/
namespace BstLean.Part266.Row12404
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12402 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12402 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12402 128 ≤ (12656 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12656 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12404) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12404 : ℕ))
    (by norm_num : (12404 : ℕ) ≤ 16384)
  have ht : paperTail256 12404 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12404 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12404 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12404 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12404 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12404 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12402 128 * √(2 / (12404 : ℝ)) *
      (√(12404 : ℝ) + paperT0 12404 + paperTail256 12404) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12404 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12404 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12404 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12402 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12402 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12404 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12404

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12404
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12404 (61 / 100) 161 (17 / (100 * 12404)) (26 / (10 * 12404)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12404 (61 / 100) 161 (17 / (100 * 12404)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (127871743 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (65977037 / 40000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (48325349 / 7812500000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12404 / 12404 * (61 / 100)) ^ 4 * inverseRadius8 (12404 - 1) /
            envelopeGap 12404 (61 / 100) 161 (17 / (100 * 12404)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12404

namespace BstLean.Part266.Row12404
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12404 161 ≤ (4861027327 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12404 161 ≤ (1621721231 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (9744533 / 25000000000000000)
  w0 : (tableEnvelope C).w0 12404 161 ≤ (983800801 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12404 161 ≤ (699955509 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12404 161 ≤ (127873241 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (127871743 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (127871743 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (65977037 / 40000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (48325349 / 7812500000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3702061 / 1000000000) : ℝ) ≤ √(17 / (100 * 12404) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12404) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1130803887 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (20306562517 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12404) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12404) ≤ (114012703 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12404) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12404 * (161 : ℝ) ^ 2 + 26 / (10 * 12404) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12404) : ℝ)) (tA 12404 * 161 ^ 2 + 26 / (10 * 12404)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3702061 / 1000000000))) * ((127871743 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3702061 / 1000000000)) ^ 3) * ((65977037 / 40000000000000000000000))) + ((48325349 / 7812500000000000000000)) * (3 / 2 * (39895 / 100000) / ((3702061 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12404) : ℝ)) d.D d.V d.P (√(tA 12404) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3702061 / 1000000000)) ^ 2 * (((1130803887 / 500000000000000)) * ((20306562517 / 500000000000000000)))) + ((48325349 / 7812500000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12404) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3702061 / 1000000000)) * ((127871743 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12404) : ℝ)) (tA 12404 * 161 ^ 2 + 26 / (10 * 12404)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((127871743 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3702061 / 1000000000)) ^ 2) * ((65977037 / 40000000000000000000000)) + ((48325349 / 7812500000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12404) : ℝ)) (√(26 / (10 * 12404) : ℝ)) d.D d.V d.P (√(tA 12404) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3702061 / 1000000000)) * (((1130803887 / 500000000000000)) * ((20306562517 / 500000000000000000))) + ((48325349 / 7812500000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12404) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((127871743 / 25000000000000000000) : ℝ) + ((48325349 / 7812500000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12404

namespace BstLean.Part266.Row12404
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12404 161 ∧
    0 ≤ (tableEnvelope C).f1 12404 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12404 161 ∧
    0 ≤ (tableEnvelope C).w1 12404 161 ∧ 0 ≤ (tableEnvelope C).w2 12404 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12404 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12404 161 ∧ 0 ≤ d.f1 12404 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12404 161 ∧ 0 ≤ d.w1 12404 161 ∧ 0 ≤ d.w2 12404 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12404 ≤ 2 * (228 / 100 : ℝ) / 12404 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12404 ≤ 2 * (370 / 100 : ℝ) / 12404 := by
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
    (completeRAData (tableEnvelope C) 12404 161).locationBound 12404 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12404 161).energyBound 12404 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12404 161) (d.f1 12404 161) d.f2 ≤
      32 * (((4861027327 / 1000000000000000000) : ℝ) + (1621721231 / 1000000000000000000) + (9744533 / 25000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12404 161) (d.w1 12404 161)
      (d.w2 12404 161) ≤
      32 * (((983800801 / 50000000000000000000) : ℝ) + (699955509 / 50000000000000000000) + (127873241 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12404 161) (d.f1 12404 161) d.f2 ≤
      ((4861027327 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4861027327 / 1000000000000000000)) * ((1621721231 / 1000000000000000000)) * (126 / 100) +
      2 * (((1621721231 / 1000000000000000000)) ^ 2 + 2 * ((4861027327 / 1000000000000000000)) * ((9744533 / 25000000000000000))) +
      6 * ((1621721231 / 1000000000000000000)) * ((9744533 / 25000000000000000)) * (126 / 100) + 8 * ((9744533 / 25000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12404 161) (d.f1 12404 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12404 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12404 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12404 161) (d.f1 12404 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12404 161) (d.w1 12404 161) (d.w2 12404 161)
  have hwexpr0 : 0 ≤ d.w0 12404 161 + d.w1 12404 161 * √(π / 2) +
      2 * d.w2 12404 161 + energyR16 12404 *
      radiusPolynomialRoot16 (d.w0 12404 161) (d.w1 12404 161) (d.w2 12404 161) := by
    positivity
  constructor
  · change (12404 : ℝ) ^ 8 * (mA 12404 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12404 161) (d.f1 12404 161) d.f2 + locationR16 12404 *
        radiusPolynomialRoot16 (d.f0 12404 161) (d.f1 12404 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12404 : ℝ) ^ 8 * (mA 12404 : ℝ) ^ 8 *
        ((((4861027327 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4861027327 / 1000000000000000000)) * ((1621721231 / 1000000000000000000)) * (126 / 100) +
          2 * (((1621721231 / 1000000000000000000)) ^ 2 + 2 * ((4861027327 / 1000000000000000000)) * ((9744533 / 25000000000000000))) +
          6 * ((1621721231 / 1000000000000000000)) * ((9744533 / 25000000000000000)) * (126 / 100) + 8 * ((9744533 / 25000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12404) *
          (32 * (((4861027327 / 1000000000000000000) : ℝ) + (1621721231 / 1000000000000000000) + (9744533 / 25000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12404 : ℝ) ^ 16 *
      (d.w0 12404 161 + d.w1 12404 161 * √(π / 2) + 2 * d.w2 12404 161 +
        energyR16 12404 * radiusPolynomialRoot16 (d.w0 12404 161) (d.w1 12404 161)
          (d.w2 12404 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12404 : ℝ) ^ 16 *
        (((983800801 / 50000000000000000000) : ℝ) + ((699955509 / 50000000000000000000)) * (126 / 100) + 2 * ((127873241 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12404) *
          (32 * (((983800801 / 50000000000000000000) : ℝ) + (699955509 / 50000000000000000000) + (127873241 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12404

/-! A coarse bound on the actual paper statistics constant at dimension 12405. -/
namespace BstLean.Part266.Row12405
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12403 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12403 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12403 128 ≤ (12657 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12657 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12405) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12405 : ℕ))
    (by norm_num : (12405 : ℕ) ≤ 16384)
  have ht : paperTail256 12405 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12405 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12405 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12405 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12405 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12405 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12403 128 * √(2 / (12405 : ℝ)) *
      (√(12405 : ℝ) + paperT0 12405 + paperTail256 12405) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12405 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12405 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12405 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12403 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12403 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12405 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12405

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12405
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12405 (61 / 100) 161 (17 / (100 * 12405)) (26 / (10 * 12405)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12405 (61 / 100) 161 (17 / (100 * 12405)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (255681639 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1648894109 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1545404237 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12405 / 12405 * (61 / 100)) ^ 4 * inverseRadius8 (12405 - 1) /
            envelopeGap 12405 (61 / 100) 161 (17 / (100 * 12405)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12405

namespace BstLean.Part266.Row12405
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12405 161 ≤ (1215012657 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12405 161 ≤ (405348771 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (6089107 / 15625000000000000)
  w0 : (tableEnvelope C).w0 12405 161 ≤ (1967126387 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12405 161 ≤ (1399572769 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12405 161 ≤ (511369267 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (255681639 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (255681639 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1648894109 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1545404237 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3701911 / 1000000000) : ℝ) ≤ √(17 / (100 * 12405) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12405) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (565333573 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (8121315433 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12405) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12405) ≤ (14250439 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12405) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12405 * (161 : ℝ) ^ 2 + 26 / (10 * 12405) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12405) : ℝ)) (tA 12405 * 161 ^ 2 + 26 / (10 * 12405)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3701911 / 1000000000))) * ((255681639 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3701911 / 1000000000)) ^ 3) * ((1648894109 / 1000000000000000000000000))) + ((1545404237 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3701911 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12405) : ℝ)) d.D d.V d.P (√(tA 12405) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3701911 / 1000000000)) ^ 2 * (((565333573 / 250000000000000)) * ((8121315433 / 200000000000000000)))) + ((1545404237 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12405) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3701911 / 1000000000)) * ((255681639 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12405) : ℝ)) (tA 12405 * 161 ^ 2 + 26 / (10 * 12405)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((255681639 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3701911 / 1000000000)) ^ 2) * ((1648894109 / 1000000000000000000000000)) + ((1545404237 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12405) : ℝ)) (√(26 / (10 * 12405) : ℝ)) d.D d.V d.P (√(tA 12405) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3701911 / 1000000000)) * (((565333573 / 250000000000000)) * ((8121315433 / 200000000000000000))) + ((1545404237 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12405) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((255681639 / 50000000000000000000) : ℝ) + ((1545404237 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12405

namespace BstLean.Part266.Row12405
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12405 161 ∧
    0 ≤ (tableEnvelope C).f1 12405 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12405 161 ∧
    0 ≤ (tableEnvelope C).w1 12405 161 ∧ 0 ≤ (tableEnvelope C).w2 12405 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12405 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12405 161 ∧ 0 ≤ d.f1 12405 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12405 161 ∧ 0 ≤ d.w1 12405 161 ∧ 0 ≤ d.w2 12405 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12405 ≤ 2 * (228 / 100 : ℝ) / 12405 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12405 ≤ 2 * (370 / 100 : ℝ) / 12405 := by
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
    (completeRAData (tableEnvelope C) 12405 161).locationBound 12405 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12405 161).energyBound 12405 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12405 161) (d.f1 12405 161) d.f2 ≤
      32 * (((1215012657 / 250000000000000000) : ℝ) + (405348771 / 250000000000000000) + (6089107 / 15625000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12405 161) (d.w1 12405 161)
      (d.w2 12405 161) ≤
      32 * (((1967126387 / 100000000000000000000) : ℝ) + (1399572769 / 100000000000000000000) + (511369267 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12405 161) (d.f1 12405 161) d.f2 ≤
      ((1215012657 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1215012657 / 250000000000000000)) * ((405348771 / 250000000000000000)) * (126 / 100) +
      2 * (((405348771 / 250000000000000000)) ^ 2 + 2 * ((1215012657 / 250000000000000000)) * ((6089107 / 15625000000000000))) +
      6 * ((405348771 / 250000000000000000)) * ((6089107 / 15625000000000000)) * (126 / 100) + 8 * ((6089107 / 15625000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12405 161) (d.f1 12405 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12405 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12405 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12405 161) (d.f1 12405 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12405 161) (d.w1 12405 161) (d.w2 12405 161)
  have hwexpr0 : 0 ≤ d.w0 12405 161 + d.w1 12405 161 * √(π / 2) +
      2 * d.w2 12405 161 + energyR16 12405 *
      radiusPolynomialRoot16 (d.w0 12405 161) (d.w1 12405 161) (d.w2 12405 161) := by
    positivity
  constructor
  · change (12405 : ℝ) ^ 8 * (mA 12405 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12405 161) (d.f1 12405 161) d.f2 + locationR16 12405 *
        radiusPolynomialRoot16 (d.f0 12405 161) (d.f1 12405 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12405 : ℝ) ^ 8 * (mA 12405 : ℝ) ^ 8 *
        ((((1215012657 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1215012657 / 250000000000000000)) * ((405348771 / 250000000000000000)) * (126 / 100) +
          2 * (((405348771 / 250000000000000000)) ^ 2 + 2 * ((1215012657 / 250000000000000000)) * ((6089107 / 15625000000000000))) +
          6 * ((405348771 / 250000000000000000)) * ((6089107 / 15625000000000000)) * (126 / 100) + 8 * ((6089107 / 15625000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12405) *
          (32 * (((1215012657 / 250000000000000000) : ℝ) + (405348771 / 250000000000000000) + (6089107 / 15625000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12405 : ℝ) ^ 16 *
      (d.w0 12405 161 + d.w1 12405 161 * √(π / 2) + 2 * d.w2 12405 161 +
        energyR16 12405 * radiusPolynomialRoot16 (d.w0 12405 161) (d.w1 12405 161)
          (d.w2 12405 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12405 : ℝ) ^ 16 *
        (((1967126387 / 100000000000000000000) : ℝ) + ((1399572769 / 100000000000000000000)) * (126 / 100) + 2 * ((511369267 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12405) *
          (32 * (((1967126387 / 100000000000000000000) : ℝ) + (1399572769 / 100000000000000000000) + (511369267 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12405

/-! A coarse bound on the actual paper statistics constant at dimension 12406. -/
namespace BstLean.Part266.Row12406
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12404 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12404 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12404 128 ≤ (12658 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12658 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12406) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12406 : ℕ))
    (by norm_num : (12406 : ℕ) ≤ 16384)
  have ht : paperTail256 12406 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12406 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12406 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12406 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12406 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12406 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12404 128 * √(2 / (12406 : ℝ)) *
      (√(12406 : ℝ) + paperT0 12406 + paperTail256 12406) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12406 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12406 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12406 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12404 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12404 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12406 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12406

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12406
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12406 (61 / 100) 161 (17 / (100 * 12406)) (26 / (10 * 12406)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12406 (61 / 100) 161 (17 / (100 * 12406)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (63904953 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (412090627 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3088796089 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12406 / 12406 * (61 / 100)) ^ 4 * inverseRadius8 (12406 - 1) /
            envelopeGap 12406 (61 / 100) 161 (17 / (100 * 12406)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12406

namespace BstLean.Part266.Row12406
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12406 161 ≤ (2429535243 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12406 161 ≤ (162106817 / 100000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (77924859 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12406 161 ≤ (1966650553 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12406 161 ≤ (69961713 / 5000000000000000000)
  w2 : (tableEnvelope C).w2 12406 161 ≤ (511245609 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (63904953 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (63904953 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (412090627 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3088796089 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1850881 / 500000000) : ℝ) ≤ √(17 / (100 * 12406) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12406) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2261060867 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40600030887 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12406) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12406) ≤ (113994323 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12406) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12406 * (161 : ℝ) ^ 2 + 26 / (10 * 12406) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12406) : ℝ)) (tA 12406 * 161 ^ 2 + 26 / (10 * 12406)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1850881 / 500000000))) * ((63904953 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1850881 / 500000000)) ^ 3) * ((412090627 / 250000000000000000000000))) + ((3088796089 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1850881 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12406) : ℝ)) d.D d.V d.P (√(tA 12406) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1850881 / 500000000)) ^ 2 * (((2261060867 / 1000000000000000)) * ((40600030887 / 1000000000000000000)))) + ((3088796089 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12406) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1850881 / 500000000)) * ((63904953 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12406) : ℝ)) (tA 12406 * 161 ^ 2 + 26 / (10 * 12406)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((63904953 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1850881 / 500000000)) ^ 2) * ((412090627 / 250000000000000000000000)) + ((3088796089 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12406) : ℝ)) (√(26 / (10 * 12406) : ℝ)) d.D d.V d.P (√(tA 12406) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1850881 / 500000000)) * (((2261060867 / 1000000000000000)) * ((40600030887 / 1000000000000000000))) + ((3088796089 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12406) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((63904953 / 12500000000000000000) : ℝ) + ((3088796089 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12406

namespace BstLean.Part266.Row12406
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12406 161 ∧
    0 ≤ (tableEnvelope C).f1 12406 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12406 161 ∧
    0 ≤ (tableEnvelope C).w1 12406 161 ∧ 0 ≤ (tableEnvelope C).w2 12406 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12406 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12406 161 ∧ 0 ≤ d.f1 12406 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12406 161 ∧ 0 ≤ d.w1 12406 161 ∧ 0 ≤ d.w2 12406 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12406 ≤ 2 * (228 / 100 : ℝ) / 12406 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12406 ≤ 2 * (370 / 100 : ℝ) / 12406 := by
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
    (completeRAData (tableEnvelope C) 12406 161).locationBound 12406 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12406 161).energyBound 12406 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12406 161) (d.f1 12406 161) d.f2 ≤
      32 * (((2429535243 / 500000000000000000) : ℝ) + (162106817 / 100000000000000000) + (77924859 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12406 161) (d.w1 12406 161)
      (d.w2 12406 161) ≤
      32 * (((1966650553 / 100000000000000000000) : ℝ) + (69961713 / 5000000000000000000) + (511245609 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12406 161) (d.f1 12406 161) d.f2 ≤
      ((2429535243 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2429535243 / 500000000000000000)) * ((162106817 / 100000000000000000)) * (126 / 100) +
      2 * (((162106817 / 100000000000000000)) ^ 2 + 2 * ((2429535243 / 500000000000000000)) * ((77924859 / 200000000000000000))) +
      6 * ((162106817 / 100000000000000000)) * ((77924859 / 200000000000000000)) * (126 / 100) + 8 * ((77924859 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12406 161) (d.f1 12406 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12406 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12406 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12406 161) (d.f1 12406 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12406 161) (d.w1 12406 161) (d.w2 12406 161)
  have hwexpr0 : 0 ≤ d.w0 12406 161 + d.w1 12406 161 * √(π / 2) +
      2 * d.w2 12406 161 + energyR16 12406 *
      radiusPolynomialRoot16 (d.w0 12406 161) (d.w1 12406 161) (d.w2 12406 161) := by
    positivity
  constructor
  · change (12406 : ℝ) ^ 8 * (mA 12406 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12406 161) (d.f1 12406 161) d.f2 + locationR16 12406 *
        radiusPolynomialRoot16 (d.f0 12406 161) (d.f1 12406 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12406 : ℝ) ^ 8 * (mA 12406 : ℝ) ^ 8 *
        ((((2429535243 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2429535243 / 500000000000000000)) * ((162106817 / 100000000000000000)) * (126 / 100) +
          2 * (((162106817 / 100000000000000000)) ^ 2 + 2 * ((2429535243 / 500000000000000000)) * ((77924859 / 200000000000000000))) +
          6 * ((162106817 / 100000000000000000)) * ((77924859 / 200000000000000000)) * (126 / 100) + 8 * ((77924859 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12406) *
          (32 * (((2429535243 / 500000000000000000) : ℝ) + (162106817 / 100000000000000000) + (77924859 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12406 : ℝ) ^ 16 *
      (d.w0 12406 161 + d.w1 12406 161 * √(π / 2) + 2 * d.w2 12406 161 +
        energyR16 12406 * radiusPolynomialRoot16 (d.w0 12406 161) (d.w1 12406 161)
          (d.w2 12406 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12406 : ℝ) ^ 16 *
        (((1966650553 / 100000000000000000000) : ℝ) + ((69961713 / 5000000000000000000)) * (126 / 100) + 2 * ((511245609 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12406) *
          (32 * (((1966650553 / 100000000000000000000) : ℝ) + (69961713 / 5000000000000000000) + (511245609 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12406

/-! A coarse bound on the actual paper statistics constant at dimension 12407. -/
namespace BstLean.Part266.Row12407
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12405 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12405 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12405 128 ≤ (12659 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12659 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12407) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12407 : ℕ))
    (by norm_num : (12407 : ℕ) ≤ 16384)
  have ht : paperTail256 12407 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12407 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12407 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12407 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12407 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12407 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12405 128 * √(2 / (12407 : ℝ)) *
      (√(12407 : ℝ) + paperT0 12407 + paperTail256 12407) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12407 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12407 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12407 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12405 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12405 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12407 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12407

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12407
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12407 (61 / 100) 161 (17 / (100 * 12407)) (26 / (10 * 12407)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12407 (61 / 100) 161 (17 / (100 * 12407)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (51111601 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1647831121 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6173570359 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12407 / 12407 * (61 / 100)) ^ 4 * inverseRadius8 (12407 - 1) /
            envelopeGap 12407 (61 / 100) 161 (17 / (100 * 12407)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12407

namespace BstLean.Part266.Row12407
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12407 161 ≤ (4858090689 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12407 161 ≤ (1620741363 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (194772883 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12407 161 ≤ (1966174887 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12407 161 ≤ (279779173 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12407 161 ≤ (511121991 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (51111601 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (51111601 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1647831121 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6173570359 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3701613 / 1000000000) : ℝ) ≤ √(17 / (100 * 12407) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12407) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (282598437 / 125000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4059348619 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12407) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12407) ≤ (22797027 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12407) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12407 * (161 : ℝ) ^ 2 + 26 / (10 * 12407) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12407) : ℝ)) (tA 12407 * 161 ^ 2 + 26 / (10 * 12407)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3701613 / 1000000000))) * ((51111601 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3701613 / 1000000000)) ^ 3) * ((1647831121 / 1000000000000000000000000))) + ((6173570359 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3701613 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12407) : ℝ)) d.D d.V d.P (√(tA 12407) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3701613 / 1000000000)) ^ 2 * (((282598437 / 125000000000000)) * ((4059348619 / 100000000000000000)))) + ((6173570359 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12407) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3701613 / 1000000000)) * ((51111601 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12407) : ℝ)) (tA 12407 * 161 ^ 2 + 26 / (10 * 12407)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((51111601 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3701613 / 1000000000)) ^ 2) * ((1647831121 / 1000000000000000000000000)) + ((6173570359 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12407) : ℝ)) (√(26 / (10 * 12407) : ℝ)) d.D d.V d.P (√(tA 12407) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3701613 / 1000000000)) * (((282598437 / 125000000000000)) * ((4059348619 / 100000000000000000))) + ((6173570359 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12407) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((51111601 / 10000000000000000000) : ℝ) + ((6173570359 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12407

namespace BstLean.Part266.Row12407
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12407 161 ∧
    0 ≤ (tableEnvelope C).f1 12407 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12407 161 ∧
    0 ≤ (tableEnvelope C).w1 12407 161 ∧ 0 ≤ (tableEnvelope C).w2 12407 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12407 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12407 161 ∧ 0 ≤ d.f1 12407 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12407 161 ∧ 0 ≤ d.w1 12407 161 ∧ 0 ≤ d.w2 12407 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12407 ≤ 2 * (228 / 100 : ℝ) / 12407 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12407 ≤ 2 * (370 / 100 : ℝ) / 12407 := by
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
    (completeRAData (tableEnvelope C) 12407 161).locationBound 12407 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12407 161).energyBound 12407 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12407 161) (d.f1 12407 161) d.f2 ≤
      32 * (((4858090689 / 1000000000000000000) : ℝ) + (1620741363 / 1000000000000000000) + (194772883 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12407 161) (d.w1 12407 161)
      (d.w2 12407 161) ≤
      32 * (((1966174887 / 100000000000000000000) : ℝ) + (279779173 / 20000000000000000000) + (511121991 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12407 161) (d.f1 12407 161) d.f2 ≤
      ((4858090689 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4858090689 / 1000000000000000000)) * ((1620741363 / 1000000000000000000)) * (126 / 100) +
      2 * (((1620741363 / 1000000000000000000)) ^ 2 + 2 * ((4858090689 / 1000000000000000000)) * ((194772883 / 500000000000000000))) +
      6 * ((1620741363 / 1000000000000000000)) * ((194772883 / 500000000000000000)) * (126 / 100) + 8 * ((194772883 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12407 161) (d.f1 12407 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12407 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12407 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12407 161) (d.f1 12407 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12407 161) (d.w1 12407 161) (d.w2 12407 161)
  have hwexpr0 : 0 ≤ d.w0 12407 161 + d.w1 12407 161 * √(π / 2) +
      2 * d.w2 12407 161 + energyR16 12407 *
      radiusPolynomialRoot16 (d.w0 12407 161) (d.w1 12407 161) (d.w2 12407 161) := by
    positivity
  constructor
  · change (12407 : ℝ) ^ 8 * (mA 12407 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12407 161) (d.f1 12407 161) d.f2 + locationR16 12407 *
        radiusPolynomialRoot16 (d.f0 12407 161) (d.f1 12407 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12407 : ℝ) ^ 8 * (mA 12407 : ℝ) ^ 8 *
        ((((4858090689 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4858090689 / 1000000000000000000)) * ((1620741363 / 1000000000000000000)) * (126 / 100) +
          2 * (((1620741363 / 1000000000000000000)) ^ 2 + 2 * ((4858090689 / 1000000000000000000)) * ((194772883 / 500000000000000000))) +
          6 * ((1620741363 / 1000000000000000000)) * ((194772883 / 500000000000000000)) * (126 / 100) + 8 * ((194772883 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12407) *
          (32 * (((4858090689 / 1000000000000000000) : ℝ) + (1620741363 / 1000000000000000000) + (194772883 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12407 : ℝ) ^ 16 *
      (d.w0 12407 161 + d.w1 12407 161 * √(π / 2) + 2 * d.w2 12407 161 +
        energyR16 12407 * radiusPolynomialRoot16 (d.w0 12407 161) (d.w1 12407 161)
          (d.w2 12407 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12407 : ℝ) ^ 16 *
        (((1966174887 / 100000000000000000000) : ℝ) + ((279779173 / 20000000000000000000)) * (126 / 100) + 2 * ((511121991 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12407) *
          (32 * (((1966174887 / 100000000000000000000) : ℝ) + (279779173 / 20000000000000000000) + (511121991 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12407

/-! A coarse bound on the actual paper statistics constant at dimension 12408. -/
namespace BstLean.Part266.Row12408
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12406 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12406 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12406 128 ≤ (12660 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12660 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12408) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12408 : ℕ))
    (by norm_num : (12408 : ℕ) ≤ 16384)
  have ht : paperTail256 12408 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12408 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12408 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12408 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12408 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12408 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12406 128 * √(2 / (12408 : ℝ)) *
      (√(12408 : ℝ) + paperT0 12408 + paperTail256 12408) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12408 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12408 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12408 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12406 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12406 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12408 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12408

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12408
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12408 (61 / 100) 161 (17 / (100 * 12408)) (26 / (10 * 12408)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12408 (61 / 100) 161 (17 / (100 * 12408)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (127748109 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (411824987 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (48199621 / 7812500000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12408 / 12408 * (61 / 100)) ^ 4 * inverseRadius8 (12408 - 1) /
            envelopeGap 12408 (61 / 100) 161 (17 / (100 * 12408)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12408

namespace BstLean.Part266.Row12408
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12408 161 ≤ (1214277809 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12408 161 ≤ (324082933 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (194733631 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12408 161 ≤ (1965699389 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12408 161 ≤ (1398557587 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12408 161 ≤ (510998413 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (127748109 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (127748109 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (411824987 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (48199621 / 7812500000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((462683 / 125000000) : ℝ) ≤ √(17 / (100 * 12408) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12408) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2260514181 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40586943073 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12408) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12408) ≤ (28493987 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12408) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12408 * (161 : ℝ) ^ 2 + 26 / (10 * 12408) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12408) : ℝ)) (tA 12408 * 161 ^ 2 + 26 / (10 * 12408)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((462683 / 125000000))) * ((127748109 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((462683 / 125000000)) ^ 3) * ((411824987 / 250000000000000000000000))) + ((48199621 / 7812500000000000000000)) * (3 / 2 * (39895 / 100000) / ((462683 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12408) : ℝ)) d.D d.V d.P (√(tA 12408) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((462683 / 125000000)) ^ 2 * (((2260514181 / 1000000000000000)) * ((40586943073 / 1000000000000000000)))) + ((48199621 / 7812500000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12408) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((462683 / 125000000)) * ((127748109 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12408) : ℝ)) (tA 12408 * 161 ^ 2 + 26 / (10 * 12408)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((127748109 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((462683 / 125000000)) ^ 2) * ((411824987 / 250000000000000000000000)) + ((48199621 / 7812500000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12408) : ℝ)) (√(26 / (10 * 12408) : ℝ)) d.D d.V d.P (√(tA 12408) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((462683 / 125000000)) * (((2260514181 / 1000000000000000)) * ((40586943073 / 1000000000000000000))) + ((48199621 / 7812500000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12408) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((127748109 / 25000000000000000000) : ℝ) + ((48199621 / 7812500000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12408

namespace BstLean.Part266.Row12408
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12408 161 ∧
    0 ≤ (tableEnvelope C).f1 12408 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12408 161 ∧
    0 ≤ (tableEnvelope C).w1 12408 161 ∧ 0 ≤ (tableEnvelope C).w2 12408 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12408 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12408 161 ∧ 0 ≤ d.f1 12408 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12408 161 ∧ 0 ≤ d.w1 12408 161 ∧ 0 ≤ d.w2 12408 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12408 ≤ 2 * (228 / 100 : ℝ) / 12408 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12408 ≤ 2 * (370 / 100 : ℝ) / 12408 := by
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
    (completeRAData (tableEnvelope C) 12408 161).locationBound 12408 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12408 161).energyBound 12408 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12408 161) (d.f1 12408 161) d.f2 ≤
      32 * (((1214277809 / 250000000000000000) : ℝ) + (324082933 / 200000000000000000) + (194733631 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12408 161) (d.w1 12408 161)
      (d.w2 12408 161) ≤
      32 * (((1965699389 / 100000000000000000000) : ℝ) + (1398557587 / 100000000000000000000) + (510998413 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12408 161) (d.f1 12408 161) d.f2 ≤
      ((1214277809 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1214277809 / 250000000000000000)) * ((324082933 / 200000000000000000)) * (126 / 100) +
      2 * (((324082933 / 200000000000000000)) ^ 2 + 2 * ((1214277809 / 250000000000000000)) * ((194733631 / 500000000000000000))) +
      6 * ((324082933 / 200000000000000000)) * ((194733631 / 500000000000000000)) * (126 / 100) + 8 * ((194733631 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12408 161) (d.f1 12408 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12408 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12408 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12408 161) (d.f1 12408 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12408 161) (d.w1 12408 161) (d.w2 12408 161)
  have hwexpr0 : 0 ≤ d.w0 12408 161 + d.w1 12408 161 * √(π / 2) +
      2 * d.w2 12408 161 + energyR16 12408 *
      radiusPolynomialRoot16 (d.w0 12408 161) (d.w1 12408 161) (d.w2 12408 161) := by
    positivity
  constructor
  · change (12408 : ℝ) ^ 8 * (mA 12408 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12408 161) (d.f1 12408 161) d.f2 + locationR16 12408 *
        radiusPolynomialRoot16 (d.f0 12408 161) (d.f1 12408 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12408 : ℝ) ^ 8 * (mA 12408 : ℝ) ^ 8 *
        ((((1214277809 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1214277809 / 250000000000000000)) * ((324082933 / 200000000000000000)) * (126 / 100) +
          2 * (((324082933 / 200000000000000000)) ^ 2 + 2 * ((1214277809 / 250000000000000000)) * ((194733631 / 500000000000000000))) +
          6 * ((324082933 / 200000000000000000)) * ((194733631 / 500000000000000000)) * (126 / 100) + 8 * ((194733631 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12408) *
          (32 * (((1214277809 / 250000000000000000) : ℝ) + (324082933 / 200000000000000000) + (194733631 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12408 : ℝ) ^ 16 *
      (d.w0 12408 161 + d.w1 12408 161 * √(π / 2) + 2 * d.w2 12408 161 +
        energyR16 12408 * radiusPolynomialRoot16 (d.w0 12408 161) (d.w1 12408 161)
          (d.w2 12408 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12408 : ℝ) ^ 16 *
        (((1965699389 / 100000000000000000000) : ℝ) + ((1398557587 / 100000000000000000000)) * (126 / 100) + 2 * ((510998413 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12408) *
          (32 * (((1965699389 / 100000000000000000000) : ℝ) + (1398557587 / 100000000000000000000) + (510998413 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12408

/-! A coarse bound on the actual paper statistics constant at dimension 12409. -/
namespace BstLean.Part266.Row12409
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12407 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12407 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12407 128 ≤ (12661 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12661 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12409) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12409 : ℕ))
    (by norm_num : (12409 : ℕ) ≤ 16384)
  have ht : paperTail256 12409 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12409 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12409 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12409 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12409 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12409 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12407 128 * √(2 / (12409 : ℝ)) *
      (√(12409 : ℝ) + paperT0 12409 + paperTail256 12409) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12409 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12409 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12409 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12407 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12407 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12409 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12409

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12409
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12409 (61 / 100) 161 (17 / (100 * 12409)) (26 / (10 * 12409)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12409 (61 / 100) 161 (17 / (100 * 12409)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (255434451 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1646768989 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6165535563 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12409 / 12409 * (61 / 100)) ^ 4 * inverseRadius8 (12409 - 1) /
            envelopeGap 12409 (61 / 100) 161 (17 / (100 * 12409)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12409

namespace BstLean.Part266.Row12409
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12409 161 ≤ (4856132127 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12409 161 ≤ (64803523 / 40000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (194694391 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12409 161 ≤ (982612029 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12409 161 ≤ (55928777 / 4000000000000000000)
  w2 : (tableEnvelope C).w2 12409 161 ≤ (4086999 / 800000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (255434451 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (255434451 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1646768989 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6165535563 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((740263 / 200000000) : ℝ) ≤ √(17 / (100 * 12409) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12409) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2260240921 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40580401539 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12409) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12409) ≤ (28491691 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12409) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12409 * (161 : ℝ) ^ 2 + 26 / (10 * 12409) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12409) : ℝ)) (tA 12409 * 161 ^ 2 + 26 / (10 * 12409)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((740263 / 200000000))) * ((255434451 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((740263 / 200000000)) ^ 3) * ((1646768989 / 1000000000000000000000000))) + ((6165535563 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((740263 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12409) : ℝ)) d.D d.V d.P (√(tA 12409) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((740263 / 200000000)) ^ 2 * (((2260240921 / 1000000000000000)) * ((40580401539 / 1000000000000000000)))) + ((6165535563 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12409) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((740263 / 200000000)) * ((255434451 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12409) : ℝ)) (tA 12409 * 161 ^ 2 + 26 / (10 * 12409)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((255434451 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((740263 / 200000000)) ^ 2) * ((1646768989 / 1000000000000000000000000)) + ((6165535563 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12409) : ℝ)) (√(26 / (10 * 12409) : ℝ)) d.D d.V d.P (√(tA 12409) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((740263 / 200000000)) * (((2260240921 / 1000000000000000)) * ((40580401539 / 1000000000000000000))) + ((6165535563 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12409) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((255434451 / 50000000000000000000) : ℝ) + ((6165535563 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12409

namespace BstLean.Part266.Row12409
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12409 161 ∧
    0 ≤ (tableEnvelope C).f1 12409 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12409 161 ∧
    0 ≤ (tableEnvelope C).w1 12409 161 ∧ 0 ≤ (tableEnvelope C).w2 12409 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12409 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12409 161 ∧ 0 ≤ d.f1 12409 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12409 161 ∧ 0 ≤ d.w1 12409 161 ∧ 0 ≤ d.w2 12409 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12409 ≤ 2 * (228 / 100 : ℝ) / 12409 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12409 ≤ 2 * (370 / 100 : ℝ) / 12409 := by
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
    (completeRAData (tableEnvelope C) 12409 161).locationBound 12409 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12409 161).energyBound 12409 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12409 161) (d.f1 12409 161) d.f2 ≤
      32 * (((4856132127 / 1000000000000000000) : ℝ) + (64803523 / 40000000000000000) + (194694391 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12409 161) (d.w1 12409 161)
      (d.w2 12409 161) ≤
      32 * (((982612029 / 50000000000000000000) : ℝ) + (55928777 / 4000000000000000000) + (4086999 / 800000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12409 161) (d.f1 12409 161) d.f2 ≤
      ((4856132127 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4856132127 / 1000000000000000000)) * ((64803523 / 40000000000000000)) * (126 / 100) +
      2 * (((64803523 / 40000000000000000)) ^ 2 + 2 * ((4856132127 / 1000000000000000000)) * ((194694391 / 500000000000000000))) +
      6 * ((64803523 / 40000000000000000)) * ((194694391 / 500000000000000000)) * (126 / 100) + 8 * ((194694391 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12409 161) (d.f1 12409 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12409 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12409 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12409 161) (d.f1 12409 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12409 161) (d.w1 12409 161) (d.w2 12409 161)
  have hwexpr0 : 0 ≤ d.w0 12409 161 + d.w1 12409 161 * √(π / 2) +
      2 * d.w2 12409 161 + energyR16 12409 *
      radiusPolynomialRoot16 (d.w0 12409 161) (d.w1 12409 161) (d.w2 12409 161) := by
    positivity
  constructor
  · change (12409 : ℝ) ^ 8 * (mA 12409 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12409 161) (d.f1 12409 161) d.f2 + locationR16 12409 *
        radiusPolynomialRoot16 (d.f0 12409 161) (d.f1 12409 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12409 : ℝ) ^ 8 * (mA 12409 : ℝ) ^ 8 *
        ((((4856132127 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4856132127 / 1000000000000000000)) * ((64803523 / 40000000000000000)) * (126 / 100) +
          2 * (((64803523 / 40000000000000000)) ^ 2 + 2 * ((4856132127 / 1000000000000000000)) * ((194694391 / 500000000000000000))) +
          6 * ((64803523 / 40000000000000000)) * ((194694391 / 500000000000000000)) * (126 / 100) + 8 * ((194694391 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12409) *
          (32 * (((4856132127 / 1000000000000000000) : ℝ) + (64803523 / 40000000000000000) + (194694391 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12409 : ℝ) ^ 16 *
      (d.w0 12409 161 + d.w1 12409 161 * √(π / 2) + 2 * d.w2 12409 161 +
        energyR16 12409 * radiusPolynomialRoot16 (d.w0 12409 161) (d.w1 12409 161)
          (d.w2 12409 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12409 : ℝ) ^ 16 *
        (((982612029 / 50000000000000000000) : ℝ) + ((55928777 / 4000000000000000000)) * (126 / 100) + 2 * ((4086999 / 800000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12409) *
          (32 * (((982612029 / 50000000000000000000) : ℝ) + (55928777 / 4000000000000000000) + (4086999 / 800000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12409

/-! A coarse bound on the actual paper statistics constant at dimension 12410. -/
namespace BstLean.Part266.Row12410
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12408 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12408 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12408 128 ≤ (12662 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12662 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12410) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12410 : ℕ))
    (by norm_num : (12410 : ℕ) ≤ 16384)
  have ht : paperTail256 12410 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12410 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12410 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12410 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12410 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12410 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12408 128 * √(2 / (12410 : ℝ)) *
      (√(12410 : ℝ) + paperT0 12410 + paperTail256 12410) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12410 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12410 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12410 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12408 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12408 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12410 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12410

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12410
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12410 (61 / 100) 161 (17 / (100 * 12410)) (26 / (10 * 12410)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12410 (61 / 100) 161 (17 / (100 * 12410)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (7980397 / 1562500000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (411559561 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3080761291 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12410 / 12410 * (61 / 100)) ^ 4 * inverseRadius8 (12410 - 1) /
            envelopeGap 12410 (61 / 100) 161 (17 / (100 * 12410)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12410

namespace BstLean.Part266.Row12410
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12410 161 ≤ (1213788341 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12410 161 ≤ (809880797 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (15572413 / 40000000000000000)
  w0 : (tableEnvelope C).w0 12410 161 ≤ (982374447 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12410 161 ≤ (1397881379 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12410 161 ≤ (510751377 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (7980397 / 1562500000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (7980397 / 1562500000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (411559561 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3080761291 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1850583 / 500000000) : ℝ) ≤ √(17 / (100 * 12410) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12410) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2259967717 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40573861587 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12410) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12410) ≤ (5697879 / 50000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12410) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12410 * (161 : ℝ) ^ 2 + 26 / (10 * 12410) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12410) : ℝ)) (tA 12410 * 161 ^ 2 + 26 / (10 * 12410)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1850583 / 500000000))) * ((7980397 / 1562500000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1850583 / 500000000)) ^ 3) * ((411559561 / 250000000000000000000000))) + ((3080761291 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1850583 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12410) : ℝ)) d.D d.V d.P (√(tA 12410) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1850583 / 500000000)) ^ 2 * (((2259967717 / 1000000000000000)) * ((40573861587 / 1000000000000000000)))) + ((3080761291 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12410) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1850583 / 500000000)) * ((7980397 / 1562500000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12410) : ℝ)) (tA 12410 * 161 ^ 2 + 26 / (10 * 12410)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((7980397 / 1562500000000000000) : ℝ) + (24198 / 100000) / (2 * ((1850583 / 500000000)) ^ 2) * ((411559561 / 250000000000000000000000)) + ((3080761291 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12410) : ℝ)) (√(26 / (10 * 12410) : ℝ)) d.D d.V d.P (√(tA 12410) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1850583 / 500000000)) * (((2259967717 / 1000000000000000)) * ((40573861587 / 1000000000000000000))) + ((3080761291 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12410) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((7980397 / 1562500000000000000) : ℝ) + ((3080761291 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12410

namespace BstLean.Part266.Row12410
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12410 161 ∧
    0 ≤ (tableEnvelope C).f1 12410 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12410 161 ∧
    0 ≤ (tableEnvelope C).w1 12410 161 ∧ 0 ≤ (tableEnvelope C).w2 12410 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12410 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12410 161 ∧ 0 ≤ d.f1 12410 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12410 161 ∧ 0 ≤ d.w1 12410 161 ∧ 0 ≤ d.w2 12410 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12410 ≤ 2 * (228 / 100 : ℝ) / 12410 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12410 ≤ 2 * (370 / 100 : ℝ) / 12410 := by
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
    (completeRAData (tableEnvelope C) 12410 161).locationBound 12410 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12410 161).energyBound 12410 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12410 161) (d.f1 12410 161) d.f2 ≤
      32 * (((1213788341 / 250000000000000000) : ℝ) + (809880797 / 500000000000000000) + (15572413 / 40000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12410 161) (d.w1 12410 161)
      (d.w2 12410 161) ≤
      32 * (((982374447 / 50000000000000000000) : ℝ) + (1397881379 / 100000000000000000000) + (510751377 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12410 161) (d.f1 12410 161) d.f2 ≤
      ((1213788341 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1213788341 / 250000000000000000)) * ((809880797 / 500000000000000000)) * (126 / 100) +
      2 * (((809880797 / 500000000000000000)) ^ 2 + 2 * ((1213788341 / 250000000000000000)) * ((15572413 / 40000000000000000))) +
      6 * ((809880797 / 500000000000000000)) * ((15572413 / 40000000000000000)) * (126 / 100) + 8 * ((15572413 / 40000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12410 161) (d.f1 12410 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12410 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12410 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12410 161) (d.f1 12410 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12410 161) (d.w1 12410 161) (d.w2 12410 161)
  have hwexpr0 : 0 ≤ d.w0 12410 161 + d.w1 12410 161 * √(π / 2) +
      2 * d.w2 12410 161 + energyR16 12410 *
      radiusPolynomialRoot16 (d.w0 12410 161) (d.w1 12410 161) (d.w2 12410 161) := by
    positivity
  constructor
  · change (12410 : ℝ) ^ 8 * (mA 12410 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12410 161) (d.f1 12410 161) d.f2 + locationR16 12410 *
        radiusPolynomialRoot16 (d.f0 12410 161) (d.f1 12410 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12410 : ℝ) ^ 8 * (mA 12410 : ℝ) ^ 8 *
        ((((1213788341 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1213788341 / 250000000000000000)) * ((809880797 / 500000000000000000)) * (126 / 100) +
          2 * (((809880797 / 500000000000000000)) ^ 2 + 2 * ((1213788341 / 250000000000000000)) * ((15572413 / 40000000000000000))) +
          6 * ((809880797 / 500000000000000000)) * ((15572413 / 40000000000000000)) * (126 / 100) + 8 * ((15572413 / 40000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12410) *
          (32 * (((1213788341 / 250000000000000000) : ℝ) + (809880797 / 500000000000000000) + (15572413 / 40000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12410 : ℝ) ^ 16 *
      (d.w0 12410 161 + d.w1 12410 161 * √(π / 2) + 2 * d.w2 12410 161 +
        energyR16 12410 * radiusPolynomialRoot16 (d.w0 12410 161) (d.w1 12410 161)
          (d.w2 12410 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12410 : ℝ) ^ 16 *
        (((982374447 / 50000000000000000000) : ℝ) + ((1397881379 / 100000000000000000000)) * (126 / 100) + 2 * ((510751377 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12410) *
          (32 * (((982374447 / 50000000000000000000) : ℝ) + (1397881379 / 100000000000000000000) + (510751377 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12410

/-! A coarse bound on the actual paper statistics constant at dimension 12411. -/
namespace BstLean.Part266.Row12411
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12409 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12409 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12409 128 ≤ (12663 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12663 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12411) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12411 : ℕ))
    (by norm_num : (12411 : ℕ) ≤ 16384)
  have ht : paperTail256 12411 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12411 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12411 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12411 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12411 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12411 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12409 128 * √(2 / (12411 : ℝ)) *
      (√(12411 : ℝ) + paperT0 12411 + paperTail256 12411) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12411 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12411 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12411 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12409 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12409 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12411 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12411

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12411
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12411 (61 / 100) 161 (17 / (100 * 12411)) (26 / (10 * 12411)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12411 (61 / 100) 161 (17 / (100 * 12411)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (510621953 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1645707713 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3078756271 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12411 / 12411 * (61 / 100)) ^ 4 * inverseRadius8 (12411 - 1) /
            envelopeGap 12411 (61 / 100) 161 (17 / (100 * 12411)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12411

namespace BstLean.Part266.Row12411
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12411 161 ≤ (4854178731 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12411 161 ≤ (809718047 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (194615999 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12411 161 ≤ (1964274683 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12411 161 ≤ (698771913 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12411 161 ≤ (255313959 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (510621953 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (510621953 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1645707713 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3078756271 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((462627 / 125000000) : ℝ) ≤ √(17 / (100 * 12411) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12411) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1129847283 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (20283661609 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12411) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12411) ≤ (56974199 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12411) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12411 * (161 : ℝ) ^ 2 + 26 / (10 * 12411) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12411) : ℝ)) (tA 12411 * 161 ^ 2 + 26 / (10 * 12411)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((462627 / 125000000))) * ((510621953 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((462627 / 125000000)) ^ 3) * ((1645707713 / 1000000000000000000000000))) + ((3078756271 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((462627 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12411) : ℝ)) d.D d.V d.P (√(tA 12411) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((462627 / 125000000)) ^ 2 * (((1129847283 / 500000000000000)) * ((20283661609 / 500000000000000000)))) + ((3078756271 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12411) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((462627 / 125000000)) * ((510621953 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12411) : ℝ)) (tA 12411 * 161 ^ 2 + 26 / (10 * 12411)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((510621953 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((462627 / 125000000)) ^ 2) * ((1645707713 / 1000000000000000000000000)) + ((3078756271 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12411) : ℝ)) (√(26 / (10 * 12411) : ℝ)) d.D d.V d.P (√(tA 12411) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((462627 / 125000000)) * (((1129847283 / 500000000000000)) * ((20283661609 / 500000000000000000))) + ((3078756271 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12411) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((510621953 / 100000000000000000000) : ℝ) + ((3078756271 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12411

namespace BstLean.Part266.Row12411
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12411 161 ∧
    0 ≤ (tableEnvelope C).f1 12411 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12411 161 ∧
    0 ≤ (tableEnvelope C).w1 12411 161 ∧ 0 ≤ (tableEnvelope C).w2 12411 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12411 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12411 161 ∧ 0 ≤ d.f1 12411 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12411 161 ∧ 0 ≤ d.w1 12411 161 ∧ 0 ≤ d.w2 12411 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12411 ≤ 2 * (228 / 100 : ℝ) / 12411 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12411 ≤ 2 * (370 / 100 : ℝ) / 12411 := by
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
    (completeRAData (tableEnvelope C) 12411 161).locationBound 12411 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12411 161).energyBound 12411 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12411 161) (d.f1 12411 161) d.f2 ≤
      32 * (((4854178731 / 1000000000000000000) : ℝ) + (809718047 / 500000000000000000) + (194615999 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12411 161) (d.w1 12411 161)
      (d.w2 12411 161) ≤
      32 * (((1964274683 / 100000000000000000000) : ℝ) + (698771913 / 50000000000000000000) + (255313959 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12411 161) (d.f1 12411 161) d.f2 ≤
      ((4854178731 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4854178731 / 1000000000000000000)) * ((809718047 / 500000000000000000)) * (126 / 100) +
      2 * (((809718047 / 500000000000000000)) ^ 2 + 2 * ((4854178731 / 1000000000000000000)) * ((194615999 / 500000000000000000))) +
      6 * ((809718047 / 500000000000000000)) * ((194615999 / 500000000000000000)) * (126 / 100) + 8 * ((194615999 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12411 161) (d.f1 12411 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12411 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12411 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12411 161) (d.f1 12411 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12411 161) (d.w1 12411 161) (d.w2 12411 161)
  have hwexpr0 : 0 ≤ d.w0 12411 161 + d.w1 12411 161 * √(π / 2) +
      2 * d.w2 12411 161 + energyR16 12411 *
      radiusPolynomialRoot16 (d.w0 12411 161) (d.w1 12411 161) (d.w2 12411 161) := by
    positivity
  constructor
  · change (12411 : ℝ) ^ 8 * (mA 12411 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12411 161) (d.f1 12411 161) d.f2 + locationR16 12411 *
        radiusPolynomialRoot16 (d.f0 12411 161) (d.f1 12411 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12411 : ℝ) ^ 8 * (mA 12411 : ℝ) ^ 8 *
        ((((4854178731 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4854178731 / 1000000000000000000)) * ((809718047 / 500000000000000000)) * (126 / 100) +
          2 * (((809718047 / 500000000000000000)) ^ 2 + 2 * ((4854178731 / 1000000000000000000)) * ((194615999 / 500000000000000000))) +
          6 * ((809718047 / 500000000000000000)) * ((194615999 / 500000000000000000)) * (126 / 100) + 8 * ((194615999 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12411) *
          (32 * (((4854178731 / 1000000000000000000) : ℝ) + (809718047 / 500000000000000000) + (194615999 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12411 : ℝ) ^ 16 *
      (d.w0 12411 161 + d.w1 12411 161 * √(π / 2) + 2 * d.w2 12411 161 +
        energyR16 12411 * radiusPolynomialRoot16 (d.w0 12411 161) (d.w1 12411 161)
          (d.w2 12411 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12411 : ℝ) ^ 16 *
        (((1964274683 / 100000000000000000000) : ℝ) + ((698771913 / 50000000000000000000)) * (126 / 100) + 2 * ((255313959 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12411) *
          (32 * (((1964274683 / 100000000000000000000) : ℝ) + (698771913 / 50000000000000000000) + (255313959 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12411

/-! A coarse bound on the actual paper statistics constant at dimension 12412. -/
namespace BstLean.Part266.Row12412
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12410 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12410 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12410 128 ≤ (12664 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12664 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12412) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12412 : ℕ))
    (by norm_num : (12412 : ℕ) ≤ 16384)
  have ht : paperTail256 12412 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12412 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12412 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12412 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12412 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12412 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12410 128 * √(2 / (12412 : ℝ)) *
      (√(12412 : ℝ) + paperT0 12412 + paperTail256 12412) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12412 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12412 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12412 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12410 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12410 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12412 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12412

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12412
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12412 (61 / 100) 161 (17 / (100 * 12412)) (26 / (10 * 12412)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12412 (61 / 100) 161 (17 / (100 * 12412)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (255249269 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (411294349 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6153505441 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12412 / 12412 * (61 / 100)) ^ 4 * inverseRadius8 (12412 - 1) /
            envelopeGap 12412 (61 / 100) 161 (17 / (100 * 12412)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12412

namespace BstLean.Part266.Row12412
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12412 161 ≤ (303325041 / 62500000000000000)
  f1 : (tableEnvelope C).f1 12412 161 ≤ (1619109827 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (389153589 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12412 161 ≤ (981899927 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12412 161 ≤ (1397206011 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12412 161 ≤ (510504499 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (255249269 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (255249269 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (411294349 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6153505441 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3700867 / 1000000000) : ℝ) ≤ √(17 / (100 * 12412) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12412) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2259421471 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40560786433 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12412) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12412) ≤ (56969609 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12412) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12412 * (161 : ℝ) ^ 2 + 26 / (10 * 12412) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12412) : ℝ)) (tA 12412 * 161 ^ 2 + 26 / (10 * 12412)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3700867 / 1000000000))) * ((255249269 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3700867 / 1000000000)) ^ 3) * ((411294349 / 250000000000000000000000))) + ((6153505441 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3700867 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12412) : ℝ)) d.D d.V d.P (√(tA 12412) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3700867 / 1000000000)) ^ 2 * (((2259421471 / 1000000000000000)) * ((40560786433 / 1000000000000000000)))) + ((6153505441 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12412) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3700867 / 1000000000)) * ((255249269 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12412) : ℝ)) (tA 12412 * 161 ^ 2 + 26 / (10 * 12412)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((255249269 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3700867 / 1000000000)) ^ 2) * ((411294349 / 250000000000000000000000)) + ((6153505441 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12412) : ℝ)) (√(26 / (10 * 12412) : ℝ)) d.D d.V d.P (√(tA 12412) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3700867 / 1000000000)) * (((2259421471 / 1000000000000000)) * ((40560786433 / 1000000000000000000))) + ((6153505441 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12412) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((255249269 / 50000000000000000000) : ℝ) + ((6153505441 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12412

namespace BstLean.Part266.Row12412
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12412 161 ∧
    0 ≤ (tableEnvelope C).f1 12412 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12412 161 ∧
    0 ≤ (tableEnvelope C).w1 12412 161 ∧ 0 ≤ (tableEnvelope C).w2 12412 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12412 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12412 161 ∧ 0 ≤ d.f1 12412 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12412 161 ∧ 0 ≤ d.w1 12412 161 ∧ 0 ≤ d.w2 12412 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12412 ≤ 2 * (228 / 100 : ℝ) / 12412 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12412 ≤ 2 * (370 / 100 : ℝ) / 12412 := by
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
    (completeRAData (tableEnvelope C) 12412 161).locationBound 12412 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12412 161).energyBound 12412 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12412 161) (d.f1 12412 161) d.f2 ≤
      32 * (((303325041 / 62500000000000000) : ℝ) + (1619109827 / 1000000000000000000) + (389153589 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12412 161) (d.w1 12412 161)
      (d.w2 12412 161) ≤
      32 * (((981899927 / 50000000000000000000) : ℝ) + (1397206011 / 100000000000000000000) + (510504499 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12412 161) (d.f1 12412 161) d.f2 ≤
      ((303325041 / 62500000000000000) : ℝ) ^ 2 + 2 * ((303325041 / 62500000000000000)) * ((1619109827 / 1000000000000000000)) * (126 / 100) +
      2 * (((1619109827 / 1000000000000000000)) ^ 2 + 2 * ((303325041 / 62500000000000000)) * ((389153589 / 1000000000000000000))) +
      6 * ((1619109827 / 1000000000000000000)) * ((389153589 / 1000000000000000000)) * (126 / 100) + 8 * ((389153589 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12412 161) (d.f1 12412 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12412 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12412 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12412 161) (d.f1 12412 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12412 161) (d.w1 12412 161) (d.w2 12412 161)
  have hwexpr0 : 0 ≤ d.w0 12412 161 + d.w1 12412 161 * √(π / 2) +
      2 * d.w2 12412 161 + energyR16 12412 *
      radiusPolynomialRoot16 (d.w0 12412 161) (d.w1 12412 161) (d.w2 12412 161) := by
    positivity
  constructor
  · change (12412 : ℝ) ^ 8 * (mA 12412 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12412 161) (d.f1 12412 161) d.f2 + locationR16 12412 *
        radiusPolynomialRoot16 (d.f0 12412 161) (d.f1 12412 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12412 : ℝ) ^ 8 * (mA 12412 : ℝ) ^ 8 *
        ((((303325041 / 62500000000000000) : ℝ) ^ 2 + 2 * ((303325041 / 62500000000000000)) * ((1619109827 / 1000000000000000000)) * (126 / 100) +
          2 * (((1619109827 / 1000000000000000000)) ^ 2 + 2 * ((303325041 / 62500000000000000)) * ((389153589 / 1000000000000000000))) +
          6 * ((1619109827 / 1000000000000000000)) * ((389153589 / 1000000000000000000)) * (126 / 100) + 8 * ((389153589 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12412) *
          (32 * (((303325041 / 62500000000000000) : ℝ) + (1619109827 / 1000000000000000000) + (389153589 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12412 : ℝ) ^ 16 *
      (d.w0 12412 161 + d.w1 12412 161 * √(π / 2) + 2 * d.w2 12412 161 +
        energyR16 12412 * radiusPolynomialRoot16 (d.w0 12412 161) (d.w1 12412 161)
          (d.w2 12412 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12412 : ℝ) ^ 16 *
        (((981899927 / 50000000000000000000) : ℝ) + ((1397206011 / 100000000000000000000)) * (126 / 100) + 2 * ((510504499 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12412) *
          (32 * (((981899927 / 50000000000000000000) : ℝ) + (1397206011 / 100000000000000000000) + (510504499 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12412

/-! A coarse bound on the actual paper statistics constant at dimension 12413. -/
namespace BstLean.Part266.Row12413
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12411 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12411 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12411 128 ≤ (12665 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12665 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12413) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12413 : ℕ))
    (by norm_num : (12413 : ℕ) ≤ 16384)
  have ht : paperTail256 12413 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12413 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12413 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12413 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12413 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12413 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12411 128 * √(2 / (12413 : ℝ)) *
      (√(12413 : ℝ) + paperT0 12413 + paperTail256 12413) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12413 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12413 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12413 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12411 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12411 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12413 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12413

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12413
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12413 (61 / 100) 161 (17 / (100 * 12413)) (26 / (10 * 12413)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12413 (61 / 100) 161 (17 / (100 * 12413)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (510375163 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (411161823 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6149501277 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12413 / 12413 * (61 / 100)) ^ 4 * inverseRadius8 (12413 - 1) /
            envelopeGap 12413 (61 / 100) 161 (17 / (100 * 12413)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12413

namespace BstLean.Part266.Row12413
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12413 161 ≤ (4852222923 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12413 161 ≤ (404695917 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (77815041 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12413 161 ≤ (245415649 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 12413 161 ≤ (1396868311 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12413 161 ≤ (1594941 / 312500000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (510375163 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (510375163 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (411161823 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6149501277 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1850359 / 500000000) : ℝ) ≤ √(17 / (100 * 12413) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12413) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2259148431 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (2027712561 / 50000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12413) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12413) ≤ (113930039 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12413) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12413 * (161 : ℝ) ^ 2 + 26 / (10 * 12413) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12413) : ℝ)) (tA 12413 * 161 ^ 2 + 26 / (10 * 12413)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1850359 / 500000000))) * ((510375163 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1850359 / 500000000)) ^ 3) * ((411161823 / 250000000000000000000000))) + ((6149501277 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1850359 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12413) : ℝ)) d.D d.V d.P (√(tA 12413) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1850359 / 500000000)) ^ 2 * (((2259148431 / 1000000000000000)) * ((2027712561 / 50000000000000000)))) + ((6149501277 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12413) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1850359 / 500000000)) * ((510375163 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12413) : ℝ)) (tA 12413 * 161 ^ 2 + 26 / (10 * 12413)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((510375163 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1850359 / 500000000)) ^ 2) * ((411161823 / 250000000000000000000000)) + ((6149501277 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12413) : ℝ)) (√(26 / (10 * 12413) : ℝ)) d.D d.V d.P (√(tA 12413) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1850359 / 500000000)) * (((2259148431 / 1000000000000000)) * ((2027712561 / 50000000000000000))) + ((6149501277 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12413) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((510375163 / 100000000000000000000) : ℝ) + ((6149501277 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12413

namespace BstLean.Part266.Row12413
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12413 161 ∧
    0 ≤ (tableEnvelope C).f1 12413 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12413 161 ∧
    0 ≤ (tableEnvelope C).w1 12413 161 ∧ 0 ≤ (tableEnvelope C).w2 12413 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12413 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12413 161 ∧ 0 ≤ d.f1 12413 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12413 161 ∧ 0 ≤ d.w1 12413 161 ∧ 0 ≤ d.w2 12413 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12413 ≤ 2 * (228 / 100 : ℝ) / 12413 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12413 ≤ 2 * (370 / 100 : ℝ) / 12413 := by
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
    (completeRAData (tableEnvelope C) 12413 161).locationBound 12413 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12413 161).energyBound 12413 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12413 161) (d.f1 12413 161) d.f2 ≤
      32 * (((4852222923 / 1000000000000000000) : ℝ) + (404695917 / 250000000000000000) + (77815041 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12413 161) (d.w1 12413 161)
      (d.w2 12413 161) ≤
      32 * (((245415649 / 12500000000000000000) : ℝ) + (1396868311 / 100000000000000000000) + (1594941 / 312500000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12413 161) (d.f1 12413 161) d.f2 ≤
      ((4852222923 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4852222923 / 1000000000000000000)) * ((404695917 / 250000000000000000)) * (126 / 100) +
      2 * (((404695917 / 250000000000000000)) ^ 2 + 2 * ((4852222923 / 1000000000000000000)) * ((77815041 / 200000000000000000))) +
      6 * ((404695917 / 250000000000000000)) * ((77815041 / 200000000000000000)) * (126 / 100) + 8 * ((77815041 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12413 161) (d.f1 12413 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12413 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12413 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12413 161) (d.f1 12413 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12413 161) (d.w1 12413 161) (d.w2 12413 161)
  have hwexpr0 : 0 ≤ d.w0 12413 161 + d.w1 12413 161 * √(π / 2) +
      2 * d.w2 12413 161 + energyR16 12413 *
      radiusPolynomialRoot16 (d.w0 12413 161) (d.w1 12413 161) (d.w2 12413 161) := by
    positivity
  constructor
  · change (12413 : ℝ) ^ 8 * (mA 12413 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12413 161) (d.f1 12413 161) d.f2 + locationR16 12413 *
        radiusPolynomialRoot16 (d.f0 12413 161) (d.f1 12413 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12413 : ℝ) ^ 8 * (mA 12413 : ℝ) ^ 8 *
        ((((4852222923 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4852222923 / 1000000000000000000)) * ((404695917 / 250000000000000000)) * (126 / 100) +
          2 * (((404695917 / 250000000000000000)) ^ 2 + 2 * ((4852222923 / 1000000000000000000)) * ((77815041 / 200000000000000000))) +
          6 * ((404695917 / 250000000000000000)) * ((77815041 / 200000000000000000)) * (126 / 100) + 8 * ((77815041 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12413) *
          (32 * (((4852222923 / 1000000000000000000) : ℝ) + (404695917 / 250000000000000000) + (77815041 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12413 : ℝ) ^ 16 *
      (d.w0 12413 161 + d.w1 12413 161 * √(π / 2) + 2 * d.w2 12413 161 +
        energyR16 12413 * radiusPolynomialRoot16 (d.w0 12413 161) (d.w1 12413 161)
          (d.w2 12413 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12413 : ℝ) ^ 16 *
        (((245415649 / 12500000000000000000) : ℝ) + ((1396868311 / 100000000000000000000)) * (126 / 100) + 2 * ((1594941 / 312500000000000000)) +
          (2 * (370 / 100 : ℝ) / 12413) *
          (32 * (((245415649 / 12500000000000000000) : ℝ) + (1396868311 / 100000000000000000000) + (1594941 / 312500000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12413

/-! A coarse bound on the actual paper statistics constant at dimension 12414. -/
namespace BstLean.Part266.Row12414
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12412 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12412 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12412 128 ≤ (12666 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12666 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12414) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12414 : ℕ))
    (by norm_num : (12414 : ℕ) ≤ 16384)
  have ht : paperTail256 12414 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12414 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12414 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12414 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12414 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12414 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12412 128 * √(2 / (12414 : ℝ)) *
      (√(12414 : ℝ) + paperT0 12414 + paperTail256 12414) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12414 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12414 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12414 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12412 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12412 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12414 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12414

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12414
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12414 (61 / 100) 161 (17 / (100 * 12414)) (26 / (10 * 12414)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12414 (61 / 100) 161 (17 / (100 * 12414)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (127562957 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1644117401 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6145500047 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12414 / 12414 * (61 / 100)) ^ 4 * inverseRadius8 (12414 - 1) /
            envelopeGap 12414 (61 / 100) 161 (17 / (100 * 12414)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12414

namespace BstLean.Part266.Row12414
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12414 161 ≤ (2425622767 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12414 161 ≤ (1618457617 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (77799369 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12414 161 ≤ (1962850697 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12414 161 ≤ (1396530727 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12414 161 ≤ (255128891 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (127562957 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (127562957 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1644117401 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6145500047 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3700569 / 1000000000) : ℝ) ≤ √(17 / (100 * 12414) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12414) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1129437723 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40547717581 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12414) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12414) ≤ (113920861 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12414) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12414 * (161 : ℝ) ^ 2 + 26 / (10 * 12414) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12414) : ℝ)) (tA 12414 * 161 ^ 2 + 26 / (10 * 12414)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3700569 / 1000000000))) * ((127562957 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3700569 / 1000000000)) ^ 3) * ((1644117401 / 1000000000000000000000000))) + ((6145500047 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3700569 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12414) : ℝ)) d.D d.V d.P (√(tA 12414) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3700569 / 1000000000)) ^ 2 * (((1129437723 / 500000000000000)) * ((40547717581 / 1000000000000000000)))) + ((6145500047 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12414) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3700569 / 1000000000)) * ((127562957 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12414) : ℝ)) (tA 12414 * 161 ^ 2 + 26 / (10 * 12414)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((127562957 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3700569 / 1000000000)) ^ 2) * ((1644117401 / 1000000000000000000000000)) + ((6145500047 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12414) : ℝ)) (√(26 / (10 * 12414) : ℝ)) d.D d.V d.P (√(tA 12414) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3700569 / 1000000000)) * (((1129437723 / 500000000000000)) * ((40547717581 / 1000000000000000000))) + ((6145500047 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12414) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((127562957 / 25000000000000000000) : ℝ) + ((6145500047 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12414

namespace BstLean.Part266.Row12414
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12414 161 ∧
    0 ≤ (tableEnvelope C).f1 12414 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12414 161 ∧
    0 ≤ (tableEnvelope C).w1 12414 161 ∧ 0 ≤ (tableEnvelope C).w2 12414 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12414 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12414 161 ∧ 0 ≤ d.f1 12414 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12414 161 ∧ 0 ≤ d.w1 12414 161 ∧ 0 ≤ d.w2 12414 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12414 ≤ 2 * (228 / 100 : ℝ) / 12414 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12414 ≤ 2 * (370 / 100 : ℝ) / 12414 := by
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
    (completeRAData (tableEnvelope C) 12414 161).locationBound 12414 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12414 161).energyBound 12414 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12414 161) (d.f1 12414 161) d.f2 ≤
      32 * (((2425622767 / 500000000000000000) : ℝ) + (1618457617 / 1000000000000000000) + (77799369 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12414 161) (d.w1 12414 161)
      (d.w2 12414 161) ≤
      32 * (((1962850697 / 100000000000000000000) : ℝ) + (1396530727 / 100000000000000000000) + (255128891 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12414 161) (d.f1 12414 161) d.f2 ≤
      ((2425622767 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2425622767 / 500000000000000000)) * ((1618457617 / 1000000000000000000)) * (126 / 100) +
      2 * (((1618457617 / 1000000000000000000)) ^ 2 + 2 * ((2425622767 / 500000000000000000)) * ((77799369 / 200000000000000000))) +
      6 * ((1618457617 / 1000000000000000000)) * ((77799369 / 200000000000000000)) * (126 / 100) + 8 * ((77799369 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12414 161) (d.f1 12414 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12414 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12414 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12414 161) (d.f1 12414 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12414 161) (d.w1 12414 161) (d.w2 12414 161)
  have hwexpr0 : 0 ≤ d.w0 12414 161 + d.w1 12414 161 * √(π / 2) +
      2 * d.w2 12414 161 + energyR16 12414 *
      radiusPolynomialRoot16 (d.w0 12414 161) (d.w1 12414 161) (d.w2 12414 161) := by
    positivity
  constructor
  · change (12414 : ℝ) ^ 8 * (mA 12414 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12414 161) (d.f1 12414 161) d.f2 + locationR16 12414 *
        radiusPolynomialRoot16 (d.f0 12414 161) (d.f1 12414 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12414 : ℝ) ^ 8 * (mA 12414 : ℝ) ^ 8 *
        ((((2425622767 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2425622767 / 500000000000000000)) * ((1618457617 / 1000000000000000000)) * (126 / 100) +
          2 * (((1618457617 / 1000000000000000000)) ^ 2 + 2 * ((2425622767 / 500000000000000000)) * ((77799369 / 200000000000000000))) +
          6 * ((1618457617 / 1000000000000000000)) * ((77799369 / 200000000000000000)) * (126 / 100) + 8 * ((77799369 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12414) *
          (32 * (((2425622767 / 500000000000000000) : ℝ) + (1618457617 / 1000000000000000000) + (77799369 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12414 : ℝ) ^ 16 *
      (d.w0 12414 161 + d.w1 12414 161 * √(π / 2) + 2 * d.w2 12414 161 +
        energyR16 12414 * radiusPolynomialRoot16 (d.w0 12414 161) (d.w1 12414 161)
          (d.w2 12414 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12414 : ℝ) ^ 16 *
        (((1962850697 / 100000000000000000000) : ℝ) + ((1396530727 / 100000000000000000000)) * (126 / 100) + 2 * ((255128891 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12414) *
          (32 * (((1962850697 / 100000000000000000000) : ℝ) + (1396530727 / 100000000000000000000) + (255128891 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12414

/-! A coarse bound on the actual paper statistics constant at dimension 12415. -/
namespace BstLean.Part266.Row12415
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12413 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12413 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12413 128 ≤ (12667 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12667 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12415) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12415 : ℕ))
    (by norm_num : (12415 : ℕ) ≤ 16384)
  have ht : paperTail256 12415 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12415 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12415 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12415 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12415 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12415 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12413 128 * √(2 / (12415 : ℝ)) *
      (√(12415 : ℝ) + paperT0 12415 + paperTail256 12415) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12415 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12415 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12415 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12413 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12413 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12415 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12415

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12415
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12415 (61 / 100) 161 (17 / (100 * 12415)) (26 / (10 * 12415)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12415 (61 / 100) 161 (17 / (100 * 12415)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (127532133 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (410896931 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1535375437 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12415 / 12415 * (61 / 100)) ^ 4 * inverseRadius8 (12415 - 1) /
            envelopeGap 12415 (61 / 100) 161 (17 / (100 * 12415)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12415

namespace BstLean.Part266.Row12415
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12415 161 ≤ (4850268489 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12415 161 ≤ (1618131673 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (97229627 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12415 161 ≤ (122648523 / 6250000000000000000)
  w1 : (tableEnvelope C).w1 12415 161 ≤ (698096629 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12415 161 ≤ (255067241 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (127532133 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (127532133 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (410896931 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1535375437 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((185021 / 50000000) : ℝ) ≤ √(17 / (100 * 12415) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12415) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (451720503 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (5067648191 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12415) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12415) ≤ (22782337 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12415) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12415 * (161 : ℝ) ^ 2 + 26 / (10 * 12415) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12415) : ℝ)) (tA 12415 * 161 ^ 2 + 26 / (10 * 12415)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((185021 / 50000000))) * ((127532133 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((185021 / 50000000)) ^ 3) * ((410896931 / 250000000000000000000000))) + ((1535375437 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((185021 / 50000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12415) : ℝ)) d.D d.V d.P (√(tA 12415) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((185021 / 50000000)) ^ 2 * (((451720503 / 200000000000000)) * ((5067648191 / 125000000000000000)))) + ((1535375437 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12415) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((185021 / 50000000)) * ((127532133 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12415) : ℝ)) (tA 12415 * 161 ^ 2 + 26 / (10 * 12415)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((127532133 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((185021 / 50000000)) ^ 2) * ((410896931 / 250000000000000000000000)) + ((1535375437 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12415) : ℝ)) (√(26 / (10 * 12415) : ℝ)) d.D d.V d.P (√(tA 12415) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((185021 / 50000000)) * (((451720503 / 200000000000000)) * ((5067648191 / 125000000000000000))) + ((1535375437 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12415) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((127532133 / 25000000000000000000) : ℝ) + ((1535375437 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12415

namespace BstLean.Part266.Row12415
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12415 161 ∧
    0 ≤ (tableEnvelope C).f1 12415 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12415 161 ∧
    0 ≤ (tableEnvelope C).w1 12415 161 ∧ 0 ≤ (tableEnvelope C).w2 12415 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12415 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12415 161 ∧ 0 ≤ d.f1 12415 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12415 161 ∧ 0 ≤ d.w1 12415 161 ∧ 0 ≤ d.w2 12415 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12415 ≤ 2 * (228 / 100 : ℝ) / 12415 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12415 ≤ 2 * (370 / 100 : ℝ) / 12415 := by
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
    (completeRAData (tableEnvelope C) 12415 161).locationBound 12415 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12415 161).energyBound 12415 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12415 161) (d.f1 12415 161) d.f2 ≤
      32 * (((4850268489 / 1000000000000000000) : ℝ) + (1618131673 / 1000000000000000000) + (97229627 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12415 161) (d.w1 12415 161)
      (d.w2 12415 161) ≤
      32 * (((122648523 / 6250000000000000000) : ℝ) + (698096629 / 50000000000000000000) + (255067241 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12415 161) (d.f1 12415 161) d.f2 ≤
      ((4850268489 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4850268489 / 1000000000000000000)) * ((1618131673 / 1000000000000000000)) * (126 / 100) +
      2 * (((1618131673 / 1000000000000000000)) ^ 2 + 2 * ((4850268489 / 1000000000000000000)) * ((97229627 / 250000000000000000))) +
      6 * ((1618131673 / 1000000000000000000)) * ((97229627 / 250000000000000000)) * (126 / 100) + 8 * ((97229627 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12415 161) (d.f1 12415 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12415 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12415 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12415 161) (d.f1 12415 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12415 161) (d.w1 12415 161) (d.w2 12415 161)
  have hwexpr0 : 0 ≤ d.w0 12415 161 + d.w1 12415 161 * √(π / 2) +
      2 * d.w2 12415 161 + energyR16 12415 *
      radiusPolynomialRoot16 (d.w0 12415 161) (d.w1 12415 161) (d.w2 12415 161) := by
    positivity
  constructor
  · change (12415 : ℝ) ^ 8 * (mA 12415 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12415 161) (d.f1 12415 161) d.f2 + locationR16 12415 *
        radiusPolynomialRoot16 (d.f0 12415 161) (d.f1 12415 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12415 : ℝ) ^ 8 * (mA 12415 : ℝ) ^ 8 *
        ((((4850268489 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4850268489 / 1000000000000000000)) * ((1618131673 / 1000000000000000000)) * (126 / 100) +
          2 * (((1618131673 / 1000000000000000000)) ^ 2 + 2 * ((4850268489 / 1000000000000000000)) * ((97229627 / 250000000000000000))) +
          6 * ((1618131673 / 1000000000000000000)) * ((97229627 / 250000000000000000)) * (126 / 100) + 8 * ((97229627 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12415) *
          (32 * (((4850268489 / 1000000000000000000) : ℝ) + (1618131673 / 1000000000000000000) + (97229627 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12415 : ℝ) ^ 16 *
      (d.w0 12415 161 + d.w1 12415 161 * √(π / 2) + 2 * d.w2 12415 161 +
        energyR16 12415 * radiusPolynomialRoot16 (d.w0 12415 161) (d.w1 12415 161)
          (d.w2 12415 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12415 : ℝ) ^ 16 *
        (((122648523 / 6250000000000000000) : ℝ) + ((698096629 / 50000000000000000000)) * (126 / 100) + 2 * ((255067241 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12415) *
          (32 * (((122648523 / 6250000000000000000) : ℝ) + (698096629 / 50000000000000000000) + (255067241 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12415

/-! A coarse bound on the actual paper statistics constant at dimension 12416. -/
namespace BstLean.Part266.Row12416
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12414 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12414 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12414 128 ≤ (12668 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12668 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12416) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12416 : ℕ))
    (by norm_num : (12416 : ℕ) ≤ 16384)
  have ht : paperTail256 12416 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12416 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12416 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12416 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12416 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12416 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12414 128 * √(2 / (12416 : ℝ)) *
      (√(12416 : ℝ) + paperT0 12416 + paperTail256 12416) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12416 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12416 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12416 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12414 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12414 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12416 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12416

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12416
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12416 (61 / 100) 161 (17 / (100 * 12416)) (26 / (10 * 12416)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12416 (61 / 100) 161 (17 / (100 * 12416)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (127501319 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1643058261 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6137506379 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12416 / 12416 * (61 / 100)) ^ 4 * inverseRadius8 (12416 - 1) /
            envelopeGap 12416 (61 / 100) 161 (17 / (100 * 12416)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12416

namespace BstLean.Part266.Row12416
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12416 161 ≤ (484929179 / 100000000000000000)
  f1 : (tableEnvelope C).f1 12416 161 ≤ (1617805837 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (77768039 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12416 161 ≤ (1961902207 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12416 161 ≤ (697927953 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12416 161 ≤ (255005611 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (127501319 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (127501319 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1643058261 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6137506379 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3700271 / 1000000000) : ℝ) ≤ √(17 / (100 * 12416) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12416) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (56458241 / 25000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40534655063 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12416) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12416) ≤ (11390251 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12416) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12416 * (161 : ℝ) ^ 2 + 26 / (10 * 12416) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12416) : ℝ)) (tA 12416 * 161 ^ 2 + 26 / (10 * 12416)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3700271 / 1000000000))) * ((127501319 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3700271 / 1000000000)) ^ 3) * ((1643058261 / 1000000000000000000000000))) + ((6137506379 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3700271 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12416) : ℝ)) d.D d.V d.P (√(tA 12416) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3700271 / 1000000000)) ^ 2 * (((56458241 / 25000000000000)) * ((40534655063 / 1000000000000000000)))) + ((6137506379 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12416) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3700271 / 1000000000)) * ((127501319 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12416) : ℝ)) (tA 12416 * 161 ^ 2 + 26 / (10 * 12416)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((127501319 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3700271 / 1000000000)) ^ 2) * ((1643058261 / 1000000000000000000000000)) + ((6137506379 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12416) : ℝ)) (√(26 / (10 * 12416) : ℝ)) d.D d.V d.P (√(tA 12416) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3700271 / 1000000000)) * (((56458241 / 25000000000000)) * ((40534655063 / 1000000000000000000))) + ((6137506379 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12416) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((127501319 / 25000000000000000000) : ℝ) + ((6137506379 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12416

namespace BstLean.Part266.Row12416
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12416 161 ∧
    0 ≤ (tableEnvelope C).f1 12416 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12416 161 ∧
    0 ≤ (tableEnvelope C).w1 12416 161 ∧ 0 ≤ (tableEnvelope C).w2 12416 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12416 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12416 161 ∧ 0 ≤ d.f1 12416 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12416 161 ∧ 0 ≤ d.w1 12416 161 ∧ 0 ≤ d.w2 12416 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12416 ≤ 2 * (228 / 100 : ℝ) / 12416 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12416 ≤ 2 * (370 / 100 : ℝ) / 12416 := by
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
    (completeRAData (tableEnvelope C) 12416 161).locationBound 12416 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12416 161).energyBound 12416 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12416 161) (d.f1 12416 161) d.f2 ≤
      32 * (((484929179 / 100000000000000000) : ℝ) + (1617805837 / 1000000000000000000) + (77768039 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12416 161) (d.w1 12416 161)
      (d.w2 12416 161) ≤
      32 * (((1961902207 / 100000000000000000000) : ℝ) + (697927953 / 50000000000000000000) + (255005611 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12416 161) (d.f1 12416 161) d.f2 ≤
      ((484929179 / 100000000000000000) : ℝ) ^ 2 + 2 * ((484929179 / 100000000000000000)) * ((1617805837 / 1000000000000000000)) * (126 / 100) +
      2 * (((1617805837 / 1000000000000000000)) ^ 2 + 2 * ((484929179 / 100000000000000000)) * ((77768039 / 200000000000000000))) +
      6 * ((1617805837 / 1000000000000000000)) * ((77768039 / 200000000000000000)) * (126 / 100) + 8 * ((77768039 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12416 161) (d.f1 12416 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12416 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12416 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12416 161) (d.f1 12416 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12416 161) (d.w1 12416 161) (d.w2 12416 161)
  have hwexpr0 : 0 ≤ d.w0 12416 161 + d.w1 12416 161 * √(π / 2) +
      2 * d.w2 12416 161 + energyR16 12416 *
      radiusPolynomialRoot16 (d.w0 12416 161) (d.w1 12416 161) (d.w2 12416 161) := by
    positivity
  constructor
  · change (12416 : ℝ) ^ 8 * (mA 12416 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12416 161) (d.f1 12416 161) d.f2 + locationR16 12416 *
        radiusPolynomialRoot16 (d.f0 12416 161) (d.f1 12416 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12416 : ℝ) ^ 8 * (mA 12416 : ℝ) ^ 8 *
        ((((484929179 / 100000000000000000) : ℝ) ^ 2 + 2 * ((484929179 / 100000000000000000)) * ((1617805837 / 1000000000000000000)) * (126 / 100) +
          2 * (((1617805837 / 1000000000000000000)) ^ 2 + 2 * ((484929179 / 100000000000000000)) * ((77768039 / 200000000000000000))) +
          6 * ((1617805837 / 1000000000000000000)) * ((77768039 / 200000000000000000)) * (126 / 100) + 8 * ((77768039 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12416) *
          (32 * (((484929179 / 100000000000000000) : ℝ) + (1617805837 / 1000000000000000000) + (77768039 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12416 : ℝ) ^ 16 *
      (d.w0 12416 161 + d.w1 12416 161 * √(π / 2) + 2 * d.w2 12416 161 +
        energyR16 12416 * radiusPolynomialRoot16 (d.w0 12416 161) (d.w1 12416 161)
          (d.w2 12416 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12416 : ℝ) ^ 16 *
        (((1961902207 / 100000000000000000000) : ℝ) + ((697927953 / 50000000000000000000)) * (126 / 100) + 2 * ((255005611 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12416) *
          (32 * (((1961902207 / 100000000000000000000) : ℝ) + (697927953 / 50000000000000000000) + (255005611 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12416

/-! A coarse bound on the actual paper statistics constant at dimension 12417. -/
namespace BstLean.Part266.Row12417
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12415 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12415 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12415 128 ≤ (12669 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12669 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12417) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12417 : ℕ))
    (by norm_num : (12417 : ℕ) ≤ 16384)
  have ht : paperTail256 12417 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12417 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12417 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12417 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12417 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12417 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12415 128 * √(2 / (12417 : ℝ)) *
      (√(12417 : ℝ) + paperT0 12417 + paperTail256 12417) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12417 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12417 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12417 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12415 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12415 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12417 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12417

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12417
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12417 (61 / 100) 161 (17 / (100 * 12417)) (26 / (10 * 12417)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12417 (61 / 100) 161 (17 / (100 * 12417)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (25494103 / 5000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (164252901 / 100000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6133513937 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12417 / 12417 * (61 / 100)) ^ 4 * inverseRadius8 (12417 - 1) /
            envelopeGap 12417 (61 / 100) 161 (17 / (100 * 12417)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12417

namespace BstLean.Part266.Row12417
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12417 161 ≤ (4848315431 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12417 161 ≤ (1617480109 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (388761907 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12417 161 ≤ (1961428213 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12417 161 ≤ (1395518669 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12417 161 ≤ (254944001 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (25494103 / 5000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (25494103 / 5000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (164252901 / 100000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6133513937 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1850061 / 500000000) : ℝ) ≤ √(17 / (100 * 12417) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12417) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (112902841 / 50000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (506601577 / 12500000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12417) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12417) ≤ (113893337 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12417) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12417 * (161 : ℝ) ^ 2 + 26 / (10 * 12417) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12417) : ℝ)) (tA 12417 * 161 ^ 2 + 26 / (10 * 12417)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1850061 / 500000000))) * ((25494103 / 5000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1850061 / 500000000)) ^ 3) * ((164252901 / 100000000000000000000000))) + ((6133513937 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1850061 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12417) : ℝ)) d.D d.V d.P (√(tA 12417) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1850061 / 500000000)) ^ 2 * (((112902841 / 50000000000000)) * ((506601577 / 12500000000000000)))) + ((6133513937 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12417) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1850061 / 500000000)) * ((25494103 / 5000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12417) : ℝ)) (tA 12417 * 161 ^ 2 + 26 / (10 * 12417)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((25494103 / 5000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1850061 / 500000000)) ^ 2) * ((164252901 / 100000000000000000000000)) + ((6133513937 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12417) : ℝ)) (√(26 / (10 * 12417) : ℝ)) d.D d.V d.P (√(tA 12417) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1850061 / 500000000)) * (((112902841 / 50000000000000)) * ((506601577 / 12500000000000000))) + ((6133513937 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12417) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((25494103 / 5000000000000000000) : ℝ) + ((6133513937 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12417

namespace BstLean.Part266.Row12417
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12417 161 ∧
    0 ≤ (tableEnvelope C).f1 12417 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12417 161 ∧
    0 ≤ (tableEnvelope C).w1 12417 161 ∧ 0 ≤ (tableEnvelope C).w2 12417 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12417 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12417 161 ∧ 0 ≤ d.f1 12417 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12417 161 ∧ 0 ≤ d.w1 12417 161 ∧ 0 ≤ d.w2 12417 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12417 ≤ 2 * (228 / 100 : ℝ) / 12417 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12417 ≤ 2 * (370 / 100 : ℝ) / 12417 := by
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
    (completeRAData (tableEnvelope C) 12417 161).locationBound 12417 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12417 161).energyBound 12417 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12417 161) (d.f1 12417 161) d.f2 ≤
      32 * (((4848315431 / 1000000000000000000) : ℝ) + (1617480109 / 1000000000000000000) + (388761907 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12417 161) (d.w1 12417 161)
      (d.w2 12417 161) ≤
      32 * (((1961428213 / 100000000000000000000) : ℝ) + (1395518669 / 100000000000000000000) + (254944001 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12417 161) (d.f1 12417 161) d.f2 ≤
      ((4848315431 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4848315431 / 1000000000000000000)) * ((1617480109 / 1000000000000000000)) * (126 / 100) +
      2 * (((1617480109 / 1000000000000000000)) ^ 2 + 2 * ((4848315431 / 1000000000000000000)) * ((388761907 / 1000000000000000000))) +
      6 * ((1617480109 / 1000000000000000000)) * ((388761907 / 1000000000000000000)) * (126 / 100) + 8 * ((388761907 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12417 161) (d.f1 12417 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12417 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12417 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12417 161) (d.f1 12417 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12417 161) (d.w1 12417 161) (d.w2 12417 161)
  have hwexpr0 : 0 ≤ d.w0 12417 161 + d.w1 12417 161 * √(π / 2) +
      2 * d.w2 12417 161 + energyR16 12417 *
      radiusPolynomialRoot16 (d.w0 12417 161) (d.w1 12417 161) (d.w2 12417 161) := by
    positivity
  constructor
  · change (12417 : ℝ) ^ 8 * (mA 12417 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12417 161) (d.f1 12417 161) d.f2 + locationR16 12417 *
        radiusPolynomialRoot16 (d.f0 12417 161) (d.f1 12417 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12417 : ℝ) ^ 8 * (mA 12417 : ℝ) ^ 8 *
        ((((4848315431 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4848315431 / 1000000000000000000)) * ((1617480109 / 1000000000000000000)) * (126 / 100) +
          2 * (((1617480109 / 1000000000000000000)) ^ 2 + 2 * ((4848315431 / 1000000000000000000)) * ((388761907 / 1000000000000000000))) +
          6 * ((1617480109 / 1000000000000000000)) * ((388761907 / 1000000000000000000)) * (126 / 100) + 8 * ((388761907 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12417) *
          (32 * (((4848315431 / 1000000000000000000) : ℝ) + (1617480109 / 1000000000000000000) + (388761907 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12417 : ℝ) ^ 16 *
      (d.w0 12417 161 + d.w1 12417 161 * √(π / 2) + 2 * d.w2 12417 161 +
        energyR16 12417 * radiusPolynomialRoot16 (d.w0 12417 161) (d.w1 12417 161)
          (d.w2 12417 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12417 : ℝ) ^ 16 *
        (((1961428213 / 100000000000000000000) : ℝ) + ((1395518669 / 100000000000000000000)) * (126 / 100) + 2 * ((254944001 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12417) *
          (32 * (((1961428213 / 100000000000000000000) : ℝ) + (1395518669 / 100000000000000000000) + (254944001 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12417

/-! A coarse bound on the actual paper statistics constant at dimension 12418. -/
namespace BstLean.Part266.Row12418
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12416 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12416 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12416 128 ≤ (12670 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12670 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12418) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12418 : ℕ))
    (by norm_num : (12418 : ℕ) ≤ 16384)
  have ht : paperTail256 12418 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12418 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12418 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12418 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12418 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12418 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12416 128 * √(2 / (12418 : ℝ)) *
      (√(12418 : ℝ) + paperT0 12418 + paperTail256 12418) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12418 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12418 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12418 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12416 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12416 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12418 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12418

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12418
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12418 (61 / 100) 161 (17 / (100 * 12418)) (26 / (10 * 12418)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12418 (61 / 100) 161 (17 / (100 * 12418)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (127439721 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1641999973 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6129524419 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12418 / 12418 * (61 / 100)) ^ 4 * inverseRadius8 (12418 - 1) /
            envelopeGap 12418 (61 / 100) 161 (17 / (100 * 12418)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12418

namespace BstLean.Part266.Row12418
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12418 161 ≤ (2423669709 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12418 161 ≤ (1617154489 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (388683643 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12418 161 ≤ (980477193 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12418 161 ≤ (348795387 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12418 161 ≤ (254882411 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (127439721 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (127439721 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1641999973 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6129524419 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3699973 / 1000000000) : ℝ) ≤ √(17 / (100 * 12418) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12418) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (282223007 / 125000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (20260799423 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12418) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12418) ≤ (56942083 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12418) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12418 * (161 : ℝ) ^ 2 + 26 / (10 * 12418) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12418) : ℝ)) (tA 12418 * 161 ^ 2 + 26 / (10 * 12418)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3699973 / 1000000000))) * ((127439721 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3699973 / 1000000000)) ^ 3) * ((1641999973 / 1000000000000000000000000))) + ((6129524419 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3699973 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12418) : ℝ)) d.D d.V d.P (√(tA 12418) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3699973 / 1000000000)) ^ 2 * (((282223007 / 125000000000000)) * ((20260799423 / 500000000000000000)))) + ((6129524419 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12418) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3699973 / 1000000000)) * ((127439721 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12418) : ℝ)) (tA 12418 * 161 ^ 2 + 26 / (10 * 12418)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((127439721 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3699973 / 1000000000)) ^ 2) * ((1641999973 / 1000000000000000000000000)) + ((6129524419 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12418) : ℝ)) (√(26 / (10 * 12418) : ℝ)) d.D d.V d.P (√(tA 12418) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3699973 / 1000000000)) * (((282223007 / 125000000000000)) * ((20260799423 / 500000000000000000))) + ((6129524419 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12418) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((127439721 / 25000000000000000000) : ℝ) + ((6129524419 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12418

namespace BstLean.Part266.Row12418
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12418 161 ∧
    0 ≤ (tableEnvelope C).f1 12418 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12418 161 ∧
    0 ≤ (tableEnvelope C).w1 12418 161 ∧ 0 ≤ (tableEnvelope C).w2 12418 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12418 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12418 161 ∧ 0 ≤ d.f1 12418 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12418 161 ∧ 0 ≤ d.w1 12418 161 ∧ 0 ≤ d.w2 12418 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12418 ≤ 2 * (228 / 100 : ℝ) / 12418 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12418 ≤ 2 * (370 / 100 : ℝ) / 12418 := by
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
    (completeRAData (tableEnvelope C) 12418 161).locationBound 12418 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12418 161).energyBound 12418 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12418 161) (d.f1 12418 161) d.f2 ≤
      32 * (((2423669709 / 500000000000000000) : ℝ) + (1617154489 / 1000000000000000000) + (388683643 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12418 161) (d.w1 12418 161)
      (d.w2 12418 161) ≤
      32 * (((980477193 / 50000000000000000000) : ℝ) + (348795387 / 25000000000000000000) + (254882411 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12418 161) (d.f1 12418 161) d.f2 ≤
      ((2423669709 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2423669709 / 500000000000000000)) * ((1617154489 / 1000000000000000000)) * (126 / 100) +
      2 * (((1617154489 / 1000000000000000000)) ^ 2 + 2 * ((2423669709 / 500000000000000000)) * ((388683643 / 1000000000000000000))) +
      6 * ((1617154489 / 1000000000000000000)) * ((388683643 / 1000000000000000000)) * (126 / 100) + 8 * ((388683643 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12418 161) (d.f1 12418 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12418 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12418 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12418 161) (d.f1 12418 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12418 161) (d.w1 12418 161) (d.w2 12418 161)
  have hwexpr0 : 0 ≤ d.w0 12418 161 + d.w1 12418 161 * √(π / 2) +
      2 * d.w2 12418 161 + energyR16 12418 *
      radiusPolynomialRoot16 (d.w0 12418 161) (d.w1 12418 161) (d.w2 12418 161) := by
    positivity
  constructor
  · change (12418 : ℝ) ^ 8 * (mA 12418 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12418 161) (d.f1 12418 161) d.f2 + locationR16 12418 *
        radiusPolynomialRoot16 (d.f0 12418 161) (d.f1 12418 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12418 : ℝ) ^ 8 * (mA 12418 : ℝ) ^ 8 *
        ((((2423669709 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2423669709 / 500000000000000000)) * ((1617154489 / 1000000000000000000)) * (126 / 100) +
          2 * (((1617154489 / 1000000000000000000)) ^ 2 + 2 * ((2423669709 / 500000000000000000)) * ((388683643 / 1000000000000000000))) +
          6 * ((1617154489 / 1000000000000000000)) * ((388683643 / 1000000000000000000)) * (126 / 100) + 8 * ((388683643 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12418) *
          (32 * (((2423669709 / 500000000000000000) : ℝ) + (1617154489 / 1000000000000000000) + (388683643 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12418 : ℝ) ^ 16 *
      (d.w0 12418 161 + d.w1 12418 161 * √(π / 2) + 2 * d.w2 12418 161 +
        energyR16 12418 * radiusPolynomialRoot16 (d.w0 12418 161) (d.w1 12418 161)
          (d.w2 12418 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12418 : ℝ) ^ 16 *
        (((980477193 / 50000000000000000000) : ℝ) + ((348795387 / 25000000000000000000)) * (126 / 100) + 2 * ((254882411 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12418) *
          (32 * (((980477193 / 50000000000000000000) : ℝ) + (348795387 / 25000000000000000000) + (254882411 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12418

/-! A coarse bound on the actual paper statistics constant at dimension 12419. -/
namespace BstLean.Part266.Row12419
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12417 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12417 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12417 128 ≤ (12671 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12671 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12419) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12419 : ℕ))
    (by norm_num : (12419 : ℕ) ≤ 16384)
  have ht : paperTail256 12419 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12419 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12419 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12419 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12419 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12419 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12417 128 * √(2 / (12419 : ℝ)) *
      (√(12419 : ℝ) + paperT0 12419 + paperTail256 12419) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12419 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12419 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12419 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12417 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12417 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12419 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12419

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12419
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12419 (61 / 100) 161 (17 / (100 * 12419)) (26 / (10 * 12419)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12419 (61 / 100) 161 (17 / (100 * 12419)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (509635747 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (410367787 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (191423057 / 31250000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12419 / 12419 * (61 / 100)) ^ 4 * inverseRadius8 (12419 - 1) /
            envelopeGap 12419 (61 / 100) 161 (17 / (100 * 12419)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12419

namespace BstLean.Part266.Row12419
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12419 161 ≤ (2423181873 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12419 161 ≤ (64673159 / 40000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (194302701 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12419 161 ≤ (78419229 / 4000000000000000000)
  w1 : (tableEnvelope C).w1 12419 161 ≤ (1394844541 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12419 161 ≤ (509641681 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (509635747 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (509635747 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (410367787 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (191423057 / 31250000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((231239 / 62500000) : ℝ) ≤ √(17 / (100 * 12419) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12419) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (451502269 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40515073097 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12419) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12419) ≤ (22774999 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12419) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12419 * (161 : ℝ) ^ 2 + 26 / (10 * 12419) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12419) : ℝ)) (tA 12419 * 161 ^ 2 + 26 / (10 * 12419)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((231239 / 62500000))) * ((509635747 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((231239 / 62500000)) ^ 3) * ((410367787 / 250000000000000000000000))) + ((191423057 / 31250000000000000000000)) * (3 / 2 * (39895 / 100000) / ((231239 / 62500000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12419) : ℝ)) d.D d.V d.P (√(tA 12419) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((231239 / 62500000)) ^ 2 * (((451502269 / 200000000000000)) * ((40515073097 / 1000000000000000000)))) + ((191423057 / 31250000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12419) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((231239 / 62500000)) * ((509635747 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12419) : ℝ)) (tA 12419 * 161 ^ 2 + 26 / (10 * 12419)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((509635747 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((231239 / 62500000)) ^ 2) * ((410367787 / 250000000000000000000000)) + ((191423057 / 31250000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12419) : ℝ)) (√(26 / (10 * 12419) : ℝ)) d.D d.V d.P (√(tA 12419) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((231239 / 62500000)) * (((451502269 / 200000000000000)) * ((40515073097 / 1000000000000000000))) + ((191423057 / 31250000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12419) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((509635747 / 100000000000000000000) : ℝ) + ((191423057 / 31250000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12419

namespace BstLean.Part266.Row12419
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12419 161 ∧
    0 ≤ (tableEnvelope C).f1 12419 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12419 161 ∧
    0 ≤ (tableEnvelope C).w1 12419 161 ∧ 0 ≤ (tableEnvelope C).w2 12419 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12419 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12419 161 ∧ 0 ≤ d.f1 12419 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12419 161 ∧ 0 ≤ d.w1 12419 161 ∧ 0 ≤ d.w2 12419 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12419 ≤ 2 * (228 / 100 : ℝ) / 12419 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12419 ≤ 2 * (370 / 100 : ℝ) / 12419 := by
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
    (completeRAData (tableEnvelope C) 12419 161).locationBound 12419 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12419 161).energyBound 12419 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12419 161) (d.f1 12419 161) d.f2 ≤
      32 * (((2423181873 / 500000000000000000) : ℝ) + (64673159 / 40000000000000000) + (194302701 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12419 161) (d.w1 12419 161)
      (d.w2 12419 161) ≤
      32 * (((78419229 / 4000000000000000000) : ℝ) + (1394844541 / 100000000000000000000) + (509641681 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12419 161) (d.f1 12419 161) d.f2 ≤
      ((2423181873 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2423181873 / 500000000000000000)) * ((64673159 / 40000000000000000)) * (126 / 100) +
      2 * (((64673159 / 40000000000000000)) ^ 2 + 2 * ((2423181873 / 500000000000000000)) * ((194302701 / 500000000000000000))) +
      6 * ((64673159 / 40000000000000000)) * ((194302701 / 500000000000000000)) * (126 / 100) + 8 * ((194302701 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12419 161) (d.f1 12419 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12419 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12419 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12419 161) (d.f1 12419 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12419 161) (d.w1 12419 161) (d.w2 12419 161)
  have hwexpr0 : 0 ≤ d.w0 12419 161 + d.w1 12419 161 * √(π / 2) +
      2 * d.w2 12419 161 + energyR16 12419 *
      radiusPolynomialRoot16 (d.w0 12419 161) (d.w1 12419 161) (d.w2 12419 161) := by
    positivity
  constructor
  · change (12419 : ℝ) ^ 8 * (mA 12419 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12419 161) (d.f1 12419 161) d.f2 + locationR16 12419 *
        radiusPolynomialRoot16 (d.f0 12419 161) (d.f1 12419 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12419 : ℝ) ^ 8 * (mA 12419 : ℝ) ^ 8 *
        ((((2423181873 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2423181873 / 500000000000000000)) * ((64673159 / 40000000000000000)) * (126 / 100) +
          2 * (((64673159 / 40000000000000000)) ^ 2 + 2 * ((2423181873 / 500000000000000000)) * ((194302701 / 500000000000000000))) +
          6 * ((64673159 / 40000000000000000)) * ((194302701 / 500000000000000000)) * (126 / 100) + 8 * ((194302701 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12419) *
          (32 * (((2423181873 / 500000000000000000) : ℝ) + (64673159 / 40000000000000000) + (194302701 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12419 : ℝ) ^ 16 *
      (d.w0 12419 161 + d.w1 12419 161 * √(π / 2) + 2 * d.w2 12419 161 +
        energyR16 12419 * radiusPolynomialRoot16 (d.w0 12419 161) (d.w1 12419 161)
          (d.w2 12419 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12419 : ℝ) ^ 16 *
        (((78419229 / 4000000000000000000) : ℝ) + ((1394844541 / 100000000000000000000)) * (126 / 100) + 2 * ((509641681 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12419) *
          (32 * (((78419229 / 4000000000000000000) : ℝ) + (1394844541 / 100000000000000000000) + (509641681 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12419

/-! A coarse bound on the actual paper statistics constant at dimension 12420. -/
namespace BstLean.Part266.Row12420
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12418 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12418 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12418 128 ≤ (12672 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12672 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12420) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12420 : ℕ))
    (by norm_num : (12420 : ℕ) ≤ 16384)
  have ht : paperTail256 12420 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12420 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12420 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12420 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12420 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12420 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12418 128 * √(2 / (12420 : ℝ)) *
      (√(12420 : ℝ) + paperT0 12420 + paperTail256 12420) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12420 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12420 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12420 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12418 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12418 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12420 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12420

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12420
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12420 (61 / 100) 161 (17 / (100 * 12420)) (26 / (10 * 12420)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12420 (61 / 100) 161 (17 / (100 * 12420)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (10190253 / 2000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1640942537 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1530388537 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12420 / 12420 * (61 / 100)) ^ 4 * inverseRadius8 (12420 - 1) /
            envelopeGap 12420 (61 / 100) 161 (17 / (100 * 12420)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12420

namespace BstLean.Part266.Row12420
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12420 161 ≤ (4845388419 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12420 161 ≤ (161650357 / 100000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (77705437 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12420 161 ≤ (1960007231 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12420 161 ≤ (27890153 / 2000000000000000000)
  w2 : (tableEnvelope C).w2 12420 161 ≤ (25475929 / 5000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (10190253 / 2000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (10190253 / 2000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1640942537 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1530388537 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((147987 / 40000000) : ℝ) ≤ √(17 / (100 * 12420) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12420) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (225723869 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (20254274469 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12420) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12420) ≤ (113865827 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12420) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12420 * (161 : ℝ) ^ 2 + 26 / (10 * 12420) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12420) : ℝ)) (tA 12420 * 161 ^ 2 + 26 / (10 * 12420)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((147987 / 40000000))) * ((10190253 / 2000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((147987 / 40000000)) ^ 3) * ((1640942537 / 1000000000000000000000000))) + ((1530388537 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((147987 / 40000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12420) : ℝ)) d.D d.V d.P (√(tA 12420) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((147987 / 40000000)) ^ 2 * (((225723869 / 100000000000000)) * ((20254274469 / 500000000000000000)))) + ((1530388537 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12420) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((147987 / 40000000)) * ((10190253 / 2000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12420) : ℝ)) (tA 12420 * 161 ^ 2 + 26 / (10 * 12420)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((10190253 / 2000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((147987 / 40000000)) ^ 2) * ((1640942537 / 1000000000000000000000000)) + ((1530388537 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12420) : ℝ)) (√(26 / (10 * 12420) : ℝ)) d.D d.V d.P (√(tA 12420) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((147987 / 40000000)) * (((225723869 / 100000000000000)) * ((20254274469 / 500000000000000000))) + ((1530388537 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12420) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((10190253 / 2000000000000000000) : ℝ) + ((1530388537 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12420

namespace BstLean.Part266.Row12420
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12420 161 ∧
    0 ≤ (tableEnvelope C).f1 12420 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12420 161 ∧
    0 ≤ (tableEnvelope C).w1 12420 161 ∧ 0 ≤ (tableEnvelope C).w2 12420 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12420 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12420 161 ∧ 0 ≤ d.f1 12420 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12420 161 ∧ 0 ≤ d.w1 12420 161 ∧ 0 ≤ d.w2 12420 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12420 ≤ 2 * (228 / 100 : ℝ) / 12420 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12420 ≤ 2 * (370 / 100 : ℝ) / 12420 := by
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
    (completeRAData (tableEnvelope C) 12420 161).locationBound 12420 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12420 161).energyBound 12420 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12420 161) (d.f1 12420 161) d.f2 ≤
      32 * (((4845388419 / 1000000000000000000) : ℝ) + (161650357 / 100000000000000000) + (77705437 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12420 161) (d.w1 12420 161)
      (d.w2 12420 161) ≤
      32 * (((1960007231 / 100000000000000000000) : ℝ) + (27890153 / 2000000000000000000) + (25475929 / 5000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12420 161) (d.f1 12420 161) d.f2 ≤
      ((4845388419 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4845388419 / 1000000000000000000)) * ((161650357 / 100000000000000000)) * (126 / 100) +
      2 * (((161650357 / 100000000000000000)) ^ 2 + 2 * ((4845388419 / 1000000000000000000)) * ((77705437 / 200000000000000000))) +
      6 * ((161650357 / 100000000000000000)) * ((77705437 / 200000000000000000)) * (126 / 100) + 8 * ((77705437 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12420 161) (d.f1 12420 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12420 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12420 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12420 161) (d.f1 12420 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12420 161) (d.w1 12420 161) (d.w2 12420 161)
  have hwexpr0 : 0 ≤ d.w0 12420 161 + d.w1 12420 161 * √(π / 2) +
      2 * d.w2 12420 161 + energyR16 12420 *
      radiusPolynomialRoot16 (d.w0 12420 161) (d.w1 12420 161) (d.w2 12420 161) := by
    positivity
  constructor
  · change (12420 : ℝ) ^ 8 * (mA 12420 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12420 161) (d.f1 12420 161) d.f2 + locationR16 12420 *
        radiusPolynomialRoot16 (d.f0 12420 161) (d.f1 12420 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12420 : ℝ) ^ 8 * (mA 12420 : ℝ) ^ 8 *
        ((((4845388419 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4845388419 / 1000000000000000000)) * ((161650357 / 100000000000000000)) * (126 / 100) +
          2 * (((161650357 / 100000000000000000)) ^ 2 + 2 * ((4845388419 / 1000000000000000000)) * ((77705437 / 200000000000000000))) +
          6 * ((161650357 / 100000000000000000)) * ((77705437 / 200000000000000000)) * (126 / 100) + 8 * ((77705437 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12420) *
          (32 * (((4845388419 / 1000000000000000000) : ℝ) + (161650357 / 100000000000000000) + (77705437 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12420 : ℝ) ^ 16 *
      (d.w0 12420 161 + d.w1 12420 161 * √(π / 2) + 2 * d.w2 12420 161 +
        energyR16 12420 * radiusPolynomialRoot16 (d.w0 12420 161) (d.w1 12420 161)
          (d.w2 12420 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12420 : ℝ) ^ 16 *
        (((1960007231 / 100000000000000000000) : ℝ) + ((27890153 / 2000000000000000000)) * (126 / 100) + 2 * ((25475929 / 5000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12420) *
          (32 * (((1960007231 / 100000000000000000000) : ℝ) + (27890153 / 2000000000000000000) + (25475929 / 5000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12420

/-! A coarse bound on the actual paper statistics constant at dimension 12421. -/
namespace BstLean.Part266.Row12421
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12419 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12419 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12419 128 ≤ (12673 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12673 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12421) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12421 : ℕ))
    (by norm_num : (12421 : ℕ) ≤ 16384)
  have ht : paperTail256 12421 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12421 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12421 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12421 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12421 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12421 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12419 128 * √(2 / (12421 : ℝ)) *
      (√(12421 : ℝ) + paperT0 12421 + paperTail256 12421) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12421 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12421 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12421 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12419 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12419 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12421 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12421

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12421
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12421 (61 / 100) 161 (17 / (100 * 12421)) (26 / (10 * 12421)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12421 (61 / 100) 161 (17 / (100 * 12421)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (63673699 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (820207069 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (611757339 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12421 / 12421 * (61 / 100)) ^ 4 * inverseRadius8 (12421 - 1) /
            envelopeGap 12421 (61 / 100) 161 (17 / (100 * 12421)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12421

namespace BstLean.Part266.Row12421
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12421 161 ≤ (4844413433 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12421 161 ≤ (161617827 / 100000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (12139031 / 31250000000000000)
  w0 : (tableEnvelope C).w0 12421 161 ≤ (1959533903 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12421 161 ≤ (1394170873 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12421 161 ≤ (509395519 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (63673699 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (63673699 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (820207069 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (611757339 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1849763 / 500000000) : ℝ) ≤ √(17 / (100 * 12421) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12421) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (282120761 / 125000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (8100405269 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12421) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12421) ≤ (5692833 / 50000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12421) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12421 * (161 : ℝ) ^ 2 + 26 / (10 * 12421) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12421) : ℝ)) (tA 12421 * 161 ^ 2 + 26 / (10 * 12421)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1849763 / 500000000))) * ((63673699 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1849763 / 500000000)) ^ 3) * ((820207069 / 500000000000000000000000))) + ((611757339 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1849763 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12421) : ℝ)) d.D d.V d.P (√(tA 12421) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1849763 / 500000000)) ^ 2 * (((282120761 / 125000000000000)) * ((8100405269 / 200000000000000000)))) + ((611757339 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12421) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1849763 / 500000000)) * ((63673699 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12421) : ℝ)) (tA 12421 * 161 ^ 2 + 26 / (10 * 12421)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((63673699 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1849763 / 500000000)) ^ 2) * ((820207069 / 500000000000000000000000)) + ((611757339 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12421) : ℝ)) (√(26 / (10 * 12421) : ℝ)) d.D d.V d.P (√(tA 12421) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1849763 / 500000000)) * (((282120761 / 125000000000000)) * ((8100405269 / 200000000000000000))) + ((611757339 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12421) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((63673699 / 12500000000000000000) : ℝ) + ((611757339 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12421

namespace BstLean.Part266.Row12421
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12421 161 ∧
    0 ≤ (tableEnvelope C).f1 12421 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12421 161 ∧
    0 ≤ (tableEnvelope C).w1 12421 161 ∧ 0 ≤ (tableEnvelope C).w2 12421 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12421 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12421 161 ∧ 0 ≤ d.f1 12421 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12421 161 ∧ 0 ≤ d.w1 12421 161 ∧ 0 ≤ d.w2 12421 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12421 ≤ 2 * (228 / 100 : ℝ) / 12421 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12421 ≤ 2 * (370 / 100 : ℝ) / 12421 := by
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
    (completeRAData (tableEnvelope C) 12421 161).locationBound 12421 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12421 161).energyBound 12421 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12421 161) (d.f1 12421 161) d.f2 ≤
      32 * (((4844413433 / 1000000000000000000) : ℝ) + (161617827 / 100000000000000000) + (12139031 / 31250000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12421 161) (d.w1 12421 161)
      (d.w2 12421 161) ≤
      32 * (((1959533903 / 100000000000000000000) : ℝ) + (1394170873 / 100000000000000000000) + (509395519 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12421 161) (d.f1 12421 161) d.f2 ≤
      ((4844413433 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4844413433 / 1000000000000000000)) * ((161617827 / 100000000000000000)) * (126 / 100) +
      2 * (((161617827 / 100000000000000000)) ^ 2 + 2 * ((4844413433 / 1000000000000000000)) * ((12139031 / 31250000000000000))) +
      6 * ((161617827 / 100000000000000000)) * ((12139031 / 31250000000000000)) * (126 / 100) + 8 * ((12139031 / 31250000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12421 161) (d.f1 12421 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12421 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12421 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12421 161) (d.f1 12421 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12421 161) (d.w1 12421 161) (d.w2 12421 161)
  have hwexpr0 : 0 ≤ d.w0 12421 161 + d.w1 12421 161 * √(π / 2) +
      2 * d.w2 12421 161 + energyR16 12421 *
      radiusPolynomialRoot16 (d.w0 12421 161) (d.w1 12421 161) (d.w2 12421 161) := by
    positivity
  constructor
  · change (12421 : ℝ) ^ 8 * (mA 12421 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12421 161) (d.f1 12421 161) d.f2 + locationR16 12421 *
        radiusPolynomialRoot16 (d.f0 12421 161) (d.f1 12421 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12421 : ℝ) ^ 8 * (mA 12421 : ℝ) ^ 8 *
        ((((4844413433 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4844413433 / 1000000000000000000)) * ((161617827 / 100000000000000000)) * (126 / 100) +
          2 * (((161617827 / 100000000000000000)) ^ 2 + 2 * ((4844413433 / 1000000000000000000)) * ((12139031 / 31250000000000000))) +
          6 * ((161617827 / 100000000000000000)) * ((12139031 / 31250000000000000)) * (126 / 100) + 8 * ((12139031 / 31250000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12421) *
          (32 * (((4844413433 / 1000000000000000000) : ℝ) + (161617827 / 100000000000000000) + (12139031 / 31250000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12421 : ℝ) ^ 16 *
      (d.w0 12421 161 + d.w1 12421 161 * √(π / 2) + 2 * d.w2 12421 161 +
        energyR16 12421 * radiusPolynomialRoot16 (d.w0 12421 161) (d.w1 12421 161)
          (d.w2 12421 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12421 : ℝ) ^ 16 *
        (((1959533903 / 100000000000000000000) : ℝ) + ((1394170873 / 100000000000000000000)) * (126 / 100) + 2 * ((509395519 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12421) *
          (32 * (((1959533903 / 100000000000000000000) : ℝ) + (1394170873 / 100000000000000000000) + (509395519 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12421

/-! A coarse bound on the actual paper statistics constant at dimension 12422. -/
namespace BstLean.Part266.Row12422
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12420 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12420 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12420 128 ≤ (12674 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12674 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12422) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12422 : ℕ))
    (by norm_num : (12422 : ℕ) ≤ 16384)
  have ht : paperTail256 12422 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12422 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12422 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12422 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12422 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12422 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12420 128 * √(2 / (12422 : ℝ)) *
      (√(12422 : ℝ) + paperT0 12422 + paperTail256 12422) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12422 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12422 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12422 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12420 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12420 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12422 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12422

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12422
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12422 (61 / 100) 161 (17 / (100 * 12422)) (26 / (10 * 12422)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12422 (61 / 100) 161 (17 / (100 * 12422)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (20370663 / 4000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (12811609 / 7812500000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6113595547 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12422 / 12422 * (61 / 100)) ^ 4 * inverseRadius8 (12422 - 1) /
            envelopeGap 12422 (61 / 100) 161 (17 / (100 * 12422)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12422

namespace BstLean.Part266.Row12422
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12422 161 ≤ (4843438791 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12422 161 ≤ (40396327 / 25000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (48546353 / 125000000000000000)
  w0 : (tableEnvelope C).w0 12422 161 ≤ (1959060743 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12422 161 ≤ (696917107 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12422 161 ≤ (254636249 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (20370663 / 4000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (20370663 / 4000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (12811609 / 7812500000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6113595547 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3699377 / 1000000000) : ℝ) ≤ √(17 / (100 * 12422) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12422) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (282086693 / 125000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40495505331 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12422) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12422) ≤ (56923747 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12422) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12422 * (161 : ℝ) ^ 2 + 26 / (10 * 12422) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12422) : ℝ)) (tA 12422 * 161 ^ 2 + 26 / (10 * 12422)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3699377 / 1000000000))) * ((20370663 / 4000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3699377 / 1000000000)) ^ 3) * ((12811609 / 7812500000000000000000))) + ((6113595547 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3699377 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12422) : ℝ)) d.D d.V d.P (√(tA 12422) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3699377 / 1000000000)) ^ 2 * (((282086693 / 125000000000000)) * ((40495505331 / 1000000000000000000)))) + ((6113595547 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12422) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3699377 / 1000000000)) * ((20370663 / 4000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12422) : ℝ)) (tA 12422 * 161 ^ 2 + 26 / (10 * 12422)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((20370663 / 4000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3699377 / 1000000000)) ^ 2) * ((12811609 / 7812500000000000000000)) + ((6113595547 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12422) : ℝ)) (√(26 / (10 * 12422) : ℝ)) d.D d.V d.P (√(tA 12422) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3699377 / 1000000000)) * (((282086693 / 125000000000000)) * ((40495505331 / 1000000000000000000))) + ((6113595547 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12422) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((20370663 / 4000000000000000000) : ℝ) + ((6113595547 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12422

namespace BstLean.Part266.Row12422
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12422 161 ∧
    0 ≤ (tableEnvelope C).f1 12422 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12422 161 ∧
    0 ≤ (tableEnvelope C).w1 12422 161 ∧ 0 ≤ (tableEnvelope C).w2 12422 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12422 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12422 161 ∧ 0 ≤ d.f1 12422 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12422 161 ∧ 0 ≤ d.w1 12422 161 ∧ 0 ≤ d.w2 12422 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12422 ≤ 2 * (228 / 100 : ℝ) / 12422 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12422 ≤ 2 * (370 / 100 : ℝ) / 12422 := by
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
    (completeRAData (tableEnvelope C) 12422 161).locationBound 12422 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12422 161).energyBound 12422 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12422 161) (d.f1 12422 161) d.f2 ≤
      32 * (((4843438791 / 1000000000000000000) : ℝ) + (40396327 / 25000000000000000) + (48546353 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12422 161) (d.w1 12422 161)
      (d.w2 12422 161) ≤
      32 * (((1959060743 / 100000000000000000000) : ℝ) + (696917107 / 50000000000000000000) + (254636249 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12422 161) (d.f1 12422 161) d.f2 ≤
      ((4843438791 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4843438791 / 1000000000000000000)) * ((40396327 / 25000000000000000)) * (126 / 100) +
      2 * (((40396327 / 25000000000000000)) ^ 2 + 2 * ((4843438791 / 1000000000000000000)) * ((48546353 / 125000000000000000))) +
      6 * ((40396327 / 25000000000000000)) * ((48546353 / 125000000000000000)) * (126 / 100) + 8 * ((48546353 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12422 161) (d.f1 12422 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12422 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12422 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12422 161) (d.f1 12422 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12422 161) (d.w1 12422 161) (d.w2 12422 161)
  have hwexpr0 : 0 ≤ d.w0 12422 161 + d.w1 12422 161 * √(π / 2) +
      2 * d.w2 12422 161 + energyR16 12422 *
      radiusPolynomialRoot16 (d.w0 12422 161) (d.w1 12422 161) (d.w2 12422 161) := by
    positivity
  constructor
  · change (12422 : ℝ) ^ 8 * (mA 12422 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12422 161) (d.f1 12422 161) d.f2 + locationR16 12422 *
        radiusPolynomialRoot16 (d.f0 12422 161) (d.f1 12422 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12422 : ℝ) ^ 8 * (mA 12422 : ℝ) ^ 8 *
        ((((4843438791 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4843438791 / 1000000000000000000)) * ((40396327 / 25000000000000000)) * (126 / 100) +
          2 * (((40396327 / 25000000000000000)) ^ 2 + 2 * ((4843438791 / 1000000000000000000)) * ((48546353 / 125000000000000000))) +
          6 * ((40396327 / 25000000000000000)) * ((48546353 / 125000000000000000)) * (126 / 100) + 8 * ((48546353 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12422) *
          (32 * (((4843438791 / 1000000000000000000) : ℝ) + (40396327 / 25000000000000000) + (48546353 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12422 : ℝ) ^ 16 *
      (d.w0 12422 161 + d.w1 12422 161 * √(π / 2) + 2 * d.w2 12422 161 +
        energyR16 12422 * radiusPolynomialRoot16 (d.w0 12422 161) (d.w1 12422 161)
          (d.w2 12422 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12422 : ℝ) ^ 16 *
        (((1959060743 / 100000000000000000000) : ℝ) + ((696917107 / 50000000000000000000)) * (126 / 100) + 2 * ((254636249 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12422) *
          (32 * (((1959060743 / 100000000000000000000) : ℝ) + (696917107 / 50000000000000000000) + (254636249 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12422

/-! A coarse bound on the actual paper statistics constant at dimension 12423. -/
namespace BstLean.Part266.Row12423
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12421 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12421 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12421 128 ≤ (12675 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12675 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12423) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12423 : ℕ))
    (by norm_num : (12423 : ℕ) ≤ 16384)
  have ht : paperTail256 12423 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12423 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12423 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12423 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12423 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12423 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12421 128 * √(2 / (12423 : ℝ)) *
      (√(12423 : ℝ) + paperT0 12423 + paperTail256 12423) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12423 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12423 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12423 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12421 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12421 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12423 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12423

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12423
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12423 (61 / 100) 161 (17 / (100 * 12423)) (26 / (10 * 12423)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12423 (61 / 100) 161 (17 / (100 * 12423)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (127285899 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (819678989 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (763702577 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12423 / 12423 * (61 / 100)) ^ 4 * inverseRadius8 (12423 - 1) /
            envelopeGap 12423 (61 / 100) 161 (17 / (100 * 12423)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12423

namespace BstLean.Part266.Row12423
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12423 161 ≤ (4842460711 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12423 161 ≤ (807763561 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (388292573 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12423 161 ≤ (489646741 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12423 161 ≤ (1393497291 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12423 161 ≤ (101829903 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (127285899 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (127285899 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (819678989 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (763702577 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3699229 / 1000000000) : ℝ) ≤ √(17 / (100 * 12423) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12423) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (564105263 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (20244492943 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12423) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12423) ≤ (11383833 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12423) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12423 * (161 : ℝ) ^ 2 + 26 / (10 * 12423) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12423) : ℝ)) (tA 12423 * 161 ^ 2 + 26 / (10 * 12423)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3699229 / 1000000000))) * ((127285899 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3699229 / 1000000000)) ^ 3) * ((819678989 / 500000000000000000000000))) + ((763702577 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3699229 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12423) : ℝ)) d.D d.V d.P (√(tA 12423) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3699229 / 1000000000)) ^ 2 * (((564105263 / 250000000000000)) * ((20244492943 / 500000000000000000)))) + ((763702577 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12423) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3699229 / 1000000000)) * ((127285899 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12423) : ℝ)) (tA 12423 * 161 ^ 2 + 26 / (10 * 12423)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((127285899 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3699229 / 1000000000)) ^ 2) * ((819678989 / 500000000000000000000000)) + ((763702577 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12423) : ℝ)) (√(26 / (10 * 12423) : ℝ)) d.D d.V d.P (√(tA 12423) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3699229 / 1000000000)) * (((564105263 / 250000000000000)) * ((20244492943 / 500000000000000000))) + ((763702577 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12423) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((127285899 / 25000000000000000000) : ℝ) + ((763702577 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12423

namespace BstLean.Part266.Row12423
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12423 161 ∧
    0 ≤ (tableEnvelope C).f1 12423 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12423 161 ∧
    0 ≤ (tableEnvelope C).w1 12423 161 ∧ 0 ≤ (tableEnvelope C).w2 12423 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12423 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12423 161 ∧ 0 ≤ d.f1 12423 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12423 161 ∧ 0 ≤ d.w1 12423 161 ∧ 0 ≤ d.w2 12423 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12423 ≤ 2 * (228 / 100 : ℝ) / 12423 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12423 ≤ 2 * (370 / 100 : ℝ) / 12423 := by
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
    (completeRAData (tableEnvelope C) 12423 161).locationBound 12423 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12423 161).energyBound 12423 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12423 161) (d.f1 12423 161) d.f2 ≤
      32 * (((4842460711 / 1000000000000000000) : ℝ) + (807763561 / 500000000000000000) + (388292573 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12423 161) (d.w1 12423 161)
      (d.w2 12423 161) ≤
      32 * (((489646741 / 25000000000000000000) : ℝ) + (1393497291 / 100000000000000000000) + (101829903 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12423 161) (d.f1 12423 161) d.f2 ≤
      ((4842460711 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4842460711 / 1000000000000000000)) * ((807763561 / 500000000000000000)) * (126 / 100) +
      2 * (((807763561 / 500000000000000000)) ^ 2 + 2 * ((4842460711 / 1000000000000000000)) * ((388292573 / 1000000000000000000))) +
      6 * ((807763561 / 500000000000000000)) * ((388292573 / 1000000000000000000)) * (126 / 100) + 8 * ((388292573 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12423 161) (d.f1 12423 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12423 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12423 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12423 161) (d.f1 12423 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12423 161) (d.w1 12423 161) (d.w2 12423 161)
  have hwexpr0 : 0 ≤ d.w0 12423 161 + d.w1 12423 161 * √(π / 2) +
      2 * d.w2 12423 161 + energyR16 12423 *
      radiusPolynomialRoot16 (d.w0 12423 161) (d.w1 12423 161) (d.w2 12423 161) := by
    positivity
  constructor
  · change (12423 : ℝ) ^ 8 * (mA 12423 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12423 161) (d.f1 12423 161) d.f2 + locationR16 12423 *
        radiusPolynomialRoot16 (d.f0 12423 161) (d.f1 12423 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12423 : ℝ) ^ 8 * (mA 12423 : ℝ) ^ 8 *
        ((((4842460711 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4842460711 / 1000000000000000000)) * ((807763561 / 500000000000000000)) * (126 / 100) +
          2 * (((807763561 / 500000000000000000)) ^ 2 + 2 * ((4842460711 / 1000000000000000000)) * ((388292573 / 1000000000000000000))) +
          6 * ((807763561 / 500000000000000000)) * ((388292573 / 1000000000000000000)) * (126 / 100) + 8 * ((388292573 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12423) *
          (32 * (((4842460711 / 1000000000000000000) : ℝ) + (807763561 / 500000000000000000) + (388292573 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12423 : ℝ) ^ 16 *
      (d.w0 12423 161 + d.w1 12423 161 * √(π / 2) + 2 * d.w2 12423 161 +
        energyR16 12423 * radiusPolynomialRoot16 (d.w0 12423 161) (d.w1 12423 161)
          (d.w2 12423 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12423 : ℝ) ^ 16 *
        (((489646741 / 25000000000000000000) : ℝ) + ((1393497291 / 100000000000000000000)) * (126 / 100) + 2 * ((101829903 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12423) *
          (32 * (((489646741 / 25000000000000000000) : ℝ) + (1393497291 / 100000000000000000000) + (101829903 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12423

/-! A coarse bound on the actual paper statistics constant at dimension 12424. -/
namespace BstLean.Part266.Row12424
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12422 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12422 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12422 128 ≤ (12676 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12676 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12424) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12424 : ℕ))
    (by norm_num : (12424 : ℕ) ≤ 16384)
  have ht : paperTail256 12424 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12424 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12424 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12424 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12424 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12424 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12422 128 * √(2 / (12424 : ℝ)) *
      (√(12424 : ℝ) + paperT0 12424 + paperTail256 12424) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12424 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12424 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12424 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12422 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12422 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12424 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12424

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12424
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12424 (61 / 100) 161 (17 / (100 * 12424)) (26 / (10 * 12424)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12424 (61 / 100) 161 (17 / (100 * 12424)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (254510329 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1638830217 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1526412149 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12424 / 12424 * (61 / 100)) ^ 4 * inverseRadius8 (12424 - 1) /
            envelopeGap 12424 (61 / 100) 161 (17 / (100 * 12424)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12424

namespace BstLean.Part266.Row12424
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12424 161 ≤ (2420743377 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12424 161 ≤ (807601073 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (388214453 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12424 161 ≤ (244764267 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 12424 161 ≤ (1393160861 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12424 161 ≤ (509026573 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (254510329 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (254510329 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1638830217 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1526412149 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((92477 / 25000000) : ℝ) ≤ √(17 / (100 * 12424) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12424) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2256148617 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40482468021 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12424) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12424) ≤ (113829167 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12424) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12424 * (161 : ℝ) ^ 2 + 26 / (10 * 12424) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12424) : ℝ)) (tA 12424 * 161 ^ 2 + 26 / (10 * 12424)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((92477 / 25000000))) * ((254510329 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((92477 / 25000000)) ^ 3) * ((1638830217 / 1000000000000000000000000))) + ((1526412149 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((92477 / 25000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12424) : ℝ)) d.D d.V d.P (√(tA 12424) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((92477 / 25000000)) ^ 2 * (((2256148617 / 1000000000000000)) * ((40482468021 / 1000000000000000000)))) + ((1526412149 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12424) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((92477 / 25000000)) * ((254510329 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12424) : ℝ)) (tA 12424 * 161 ^ 2 + 26 / (10 * 12424)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((254510329 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((92477 / 25000000)) ^ 2) * ((1638830217 / 1000000000000000000000000)) + ((1526412149 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12424) : ℝ)) (√(26 / (10 * 12424) : ℝ)) d.D d.V d.P (√(tA 12424) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((92477 / 25000000)) * (((2256148617 / 1000000000000000)) * ((40482468021 / 1000000000000000000))) + ((1526412149 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12424) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((254510329 / 50000000000000000000) : ℝ) + ((1526412149 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12424

namespace BstLean.Part266.Row12424
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12424 161 ∧
    0 ≤ (tableEnvelope C).f1 12424 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12424 161 ∧
    0 ≤ (tableEnvelope C).w1 12424 161 ∧ 0 ≤ (tableEnvelope C).w2 12424 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12424 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12424 161 ∧ 0 ≤ d.f1 12424 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12424 161 ∧ 0 ≤ d.w1 12424 161 ∧ 0 ≤ d.w2 12424 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12424 ≤ 2 * (228 / 100 : ℝ) / 12424 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12424 ≤ 2 * (370 / 100 : ℝ) / 12424 := by
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
    (completeRAData (tableEnvelope C) 12424 161).locationBound 12424 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12424 161).energyBound 12424 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12424 161) (d.f1 12424 161) d.f2 ≤
      32 * (((2420743377 / 500000000000000000) : ℝ) + (807601073 / 500000000000000000) + (388214453 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12424 161) (d.w1 12424 161)
      (d.w2 12424 161) ≤
      32 * (((244764267 / 12500000000000000000) : ℝ) + (1393160861 / 100000000000000000000) + (509026573 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12424 161) (d.f1 12424 161) d.f2 ≤
      ((2420743377 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2420743377 / 500000000000000000)) * ((807601073 / 500000000000000000)) * (126 / 100) +
      2 * (((807601073 / 500000000000000000)) ^ 2 + 2 * ((2420743377 / 500000000000000000)) * ((388214453 / 1000000000000000000))) +
      6 * ((807601073 / 500000000000000000)) * ((388214453 / 1000000000000000000)) * (126 / 100) + 8 * ((388214453 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12424 161) (d.f1 12424 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12424 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12424 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12424 161) (d.f1 12424 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12424 161) (d.w1 12424 161) (d.w2 12424 161)
  have hwexpr0 : 0 ≤ d.w0 12424 161 + d.w1 12424 161 * √(π / 2) +
      2 * d.w2 12424 161 + energyR16 12424 *
      radiusPolynomialRoot16 (d.w0 12424 161) (d.w1 12424 161) (d.w2 12424 161) := by
    positivity
  constructor
  · change (12424 : ℝ) ^ 8 * (mA 12424 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12424 161) (d.f1 12424 161) d.f2 + locationR16 12424 *
        radiusPolynomialRoot16 (d.f0 12424 161) (d.f1 12424 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12424 : ℝ) ^ 8 * (mA 12424 : ℝ) ^ 8 *
        ((((2420743377 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2420743377 / 500000000000000000)) * ((807601073 / 500000000000000000)) * (126 / 100) +
          2 * (((807601073 / 500000000000000000)) ^ 2 + 2 * ((2420743377 / 500000000000000000)) * ((388214453 / 1000000000000000000))) +
          6 * ((807601073 / 500000000000000000)) * ((388214453 / 1000000000000000000)) * (126 / 100) + 8 * ((388214453 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12424) *
          (32 * (((2420743377 / 500000000000000000) : ℝ) + (807601073 / 500000000000000000) + (388214453 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12424 : ℝ) ^ 16 *
      (d.w0 12424 161 + d.w1 12424 161 * √(π / 2) + 2 * d.w2 12424 161 +
        energyR16 12424 * radiusPolynomialRoot16 (d.w0 12424 161) (d.w1 12424 161)
          (d.w2 12424 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12424 : ℝ) ^ 16 *
        (((244764267 / 12500000000000000000) : ℝ) + ((1393160861 / 100000000000000000000)) * (126 / 100) + 2 * ((509026573 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12424) *
          (32 * (((244764267 / 12500000000000000000) : ℝ) + (1393160861 / 100000000000000000000) + (509026573 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12424
