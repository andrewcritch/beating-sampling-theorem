import BstLean.Part266Shard12Step4


/-! A coarse bound on the actual paper statistics constant at dimension 12650. -/
namespace BstLean.Part266.Row12650
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12648 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12648 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12648 128 ≤ (12902 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12902 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12650) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12650 : ℕ))
    (by norm_num : (12650 : ℕ) ≤ 16384)
  have ht : paperTail256 12650 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12650 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12650 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12650 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12650 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12650 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12648 128 * √(2 / (12650 : ℝ)) *
      (√(12650 : ℝ) + paperT0 12650 + paperTail256 12650) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12650 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12650 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12650 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12648 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12648 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12650 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12650

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12650
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12650 (61 / 100) 162 (17 / (100 * 12650)) (26 / (10 * 12650)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12650 (61 / 100) 162 (17 / (100 * 12650)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (241110939 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (304962457 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5280686369 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12650 / 12650 * (61 / 100)) ^ 4 * inverseRadius8 (12650 - 1) /
            envelopeGap 12650 (61 / 100) 162 (17 / (100 * 12650)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12650

namespace BstLean.Part266.Row12650
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12650 162 ≤ (4628121577 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12650 162 ≤ (154401989 / 100000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (371105793 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12650 162 ≤ (927511853 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12650 162 ≤ (1319814003 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12650 162 ≤ (241113497 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (241110939 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (241110939 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (304962457 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5280686369 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((114559 / 31250000) : ℝ) ≤ √(17 / (100 * 12650) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12650) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (274494387 / 125000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19524422431 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12650) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12650) ≤ (111795539 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12650) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12650 * (162 : ℝ) ^ 2 + 26 / (10 * 12650) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12650) : ℝ)) (tA 12650 * 162 ^ 2 + 26 / (10 * 12650)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((114559 / 31250000))) * ((241110939 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((114559 / 31250000)) ^ 3) * ((304962457 / 200000000000000000000000))) + ((5280686369 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((114559 / 31250000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12650) : ℝ)) d.D d.V d.P (√(tA 12650) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((114559 / 31250000)) ^ 2 * (((274494387 / 125000000000000)) * ((19524422431 / 500000000000000000)))) + ((5280686369 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12650) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((114559 / 31250000)) * ((241110939 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12650) : ℝ)) (tA 12650 * 162 ^ 2 + 26 / (10 * 12650)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((241110939 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((114559 / 31250000)) ^ 2) * ((304962457 / 200000000000000000000000)) + ((5280686369 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12650) : ℝ)) (√(26 / (10 * 12650) : ℝ)) d.D d.V d.P (√(tA 12650) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((114559 / 31250000)) * (((274494387 / 125000000000000)) * ((19524422431 / 500000000000000000))) + ((5280686369 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12650) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((241110939 / 50000000000000000000) : ℝ) + ((5280686369 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12650

namespace BstLean.Part266.Row12650
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12650 162 ∧
    0 ≤ (tableEnvelope C).f1 12650 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12650 162 ∧
    0 ≤ (tableEnvelope C).w1 12650 162 ∧ 0 ≤ (tableEnvelope C).w2 12650 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12650 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12650 162 ∧ 0 ≤ d.f1 12650 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12650 162 ∧ 0 ≤ d.w1 12650 162 ∧ 0 ≤ d.w2 12650 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12650 ≤ 2 * (228 / 100 : ℝ) / 12650 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12650 ≤ 2 * (370 / 100 : ℝ) / 12650 := by
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
    (completeRAData (tableEnvelope C) 12650 162).locationBound 12650 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12650 162).energyBound 12650 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12650 162) (d.f1 12650 162) d.f2 ≤
      32 * (((4628121577 / 1000000000000000000) : ℝ) + (154401989 / 100000000000000000) + (371105793 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12650 162) (d.w1 12650 162)
      (d.w2 12650 162) ≤
      32 * (((927511853 / 50000000000000000000) : ℝ) + (1319814003 / 100000000000000000000) + (241113497 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12650 162) (d.f1 12650 162) d.f2 ≤
      ((4628121577 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4628121577 / 1000000000000000000)) * ((154401989 / 100000000000000000)) * (126 / 100) +
      2 * (((154401989 / 100000000000000000)) ^ 2 + 2 * ((4628121577 / 1000000000000000000)) * ((371105793 / 1000000000000000000))) +
      6 * ((154401989 / 100000000000000000)) * ((371105793 / 1000000000000000000)) * (126 / 100) + 8 * ((371105793 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12650 162) (d.f1 12650 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12650 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12650 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12650 162) (d.f1 12650 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12650 162) (d.w1 12650 162) (d.w2 12650 162)
  have hwexpr0 : 0 ≤ d.w0 12650 162 + d.w1 12650 162 * √(π / 2) +
      2 * d.w2 12650 162 + energyR16 12650 *
      radiusPolynomialRoot16 (d.w0 12650 162) (d.w1 12650 162) (d.w2 12650 162) := by
    positivity
  constructor
  · change (12650 : ℝ) ^ 8 * (mA 12650 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12650 162) (d.f1 12650 162) d.f2 + locationR16 12650 *
        radiusPolynomialRoot16 (d.f0 12650 162) (d.f1 12650 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12650 : ℝ) ^ 8 * (mA 12650 : ℝ) ^ 8 *
        ((((4628121577 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4628121577 / 1000000000000000000)) * ((154401989 / 100000000000000000)) * (126 / 100) +
          2 * (((154401989 / 100000000000000000)) ^ 2 + 2 * ((4628121577 / 1000000000000000000)) * ((371105793 / 1000000000000000000))) +
          6 * ((154401989 / 100000000000000000)) * ((371105793 / 1000000000000000000)) * (126 / 100) + 8 * ((371105793 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12650) *
          (32 * (((4628121577 / 1000000000000000000) : ℝ) + (154401989 / 100000000000000000) + (371105793 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12650 : ℝ) ^ 16 *
      (d.w0 12650 162 + d.w1 12650 162 * √(π / 2) + 2 * d.w2 12650 162 +
        energyR16 12650 * radiusPolynomialRoot16 (d.w0 12650 162) (d.w1 12650 162)
          (d.w2 12650 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12650 : ℝ) ^ 16 *
        (((927511853 / 50000000000000000000) : ℝ) + ((1319814003 / 100000000000000000000)) * (126 / 100) + 2 * ((241113497 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12650) *
          (32 * (((927511853 / 50000000000000000000) : ℝ) + (1319814003 / 100000000000000000000) + (241113497 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12650

/-! A coarse bound on the actual paper statistics constant at dimension 12651. -/
namespace BstLean.Part266.Row12651
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12649 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12649 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12649 128 ≤ (12903 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12903 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12651) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12651 : ℕ))
    (by norm_num : (12651 : ℕ) ≤ 16384)
  have ht : paperTail256 12651 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12651 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12651 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12651 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12651 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12651 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12649 128 * √(2 / (12651 : ℝ)) *
      (√(12651 : ℝ) + paperT0 12651 + paperTail256 12651) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12651 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12651 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12651 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12649 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12649 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12651 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12651

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12651
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12651 (61 / 100) 162 (17 / (100 * 12651)) (26 / (10 * 12651)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12651 (61 / 100) 162 (17 / (100 * 12651)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (482107529 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1524330207 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (659664453 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12651 / 12651 * (61 / 100)) ^ 4 * inverseRadius8 (12651 - 1) /
            envelopeGap 12651 (61 / 100) 162 (17 / (100 * 12651)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12651

namespace BstLean.Part266.Row12651
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12651 162 ≤ (1156801851 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12651 162 ≤ (96482179 / 62500000000000000)
  f2 : (tableEnvelope C).f2 ≤ (92758117 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12651 162 ≤ (1854583909 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12651 162 ≤ (329875269 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12651 162 ≤ (241056321 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (482107529 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (482107529 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1524330207 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (659664453 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3665743 / 1000000000) : ℝ) ≤ √(17 / (100 * 12651) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12651) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2195694717 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19521335809 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12651) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12651) ≤ (55893351 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12651) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12651 * (162 : ℝ) ^ 2 + 26 / (10 * 12651) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12651) : ℝ)) (tA 12651 * 162 ^ 2 + 26 / (10 * 12651)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3665743 / 1000000000))) * ((482107529 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3665743 / 1000000000)) ^ 3) * ((1524330207 / 1000000000000000000000000))) + ((659664453 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3665743 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12651) : ℝ)) d.D d.V d.P (√(tA 12651) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3665743 / 1000000000)) ^ 2 * (((2195694717 / 1000000000000000)) * ((19521335809 / 500000000000000000)))) + ((659664453 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12651) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3665743 / 1000000000)) * ((482107529 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12651) : ℝ)) (tA 12651 * 162 ^ 2 + 26 / (10 * 12651)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((482107529 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3665743 / 1000000000)) ^ 2) * ((1524330207 / 1000000000000000000000000)) + ((659664453 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12651) : ℝ)) (√(26 / (10 * 12651) : ℝ)) d.D d.V d.P (√(tA 12651) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3665743 / 1000000000)) * (((2195694717 / 1000000000000000)) * ((19521335809 / 500000000000000000))) + ((659664453 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12651) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((482107529 / 100000000000000000000) : ℝ) + ((659664453 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12651

namespace BstLean.Part266.Row12651
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12651 162 ∧
    0 ≤ (tableEnvelope C).f1 12651 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12651 162 ∧
    0 ≤ (tableEnvelope C).w1 12651 162 ∧ 0 ≤ (tableEnvelope C).w2 12651 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12651 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12651 162 ∧ 0 ≤ d.f1 12651 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12651 162 ∧ 0 ≤ d.w1 12651 162 ∧ 0 ≤ d.w2 12651 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12651 ≤ 2 * (228 / 100 : ℝ) / 12651 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12651 ≤ 2 * (370 / 100 : ℝ) / 12651 := by
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
    (completeRAData (tableEnvelope C) 12651 162).locationBound 12651 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12651 162).energyBound 12651 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12651 162) (d.f1 12651 162) d.f2 ≤
      32 * (((1156801851 / 250000000000000000) : ℝ) + (96482179 / 62500000000000000) + (92758117 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12651 162) (d.w1 12651 162)
      (d.w2 12651 162) ≤
      32 * (((1854583909 / 100000000000000000000) : ℝ) + (329875269 / 25000000000000000000) + (241056321 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12651 162) (d.f1 12651 162) d.f2 ≤
      ((1156801851 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1156801851 / 250000000000000000)) * ((96482179 / 62500000000000000)) * (126 / 100) +
      2 * (((96482179 / 62500000000000000)) ^ 2 + 2 * ((1156801851 / 250000000000000000)) * ((92758117 / 250000000000000000))) +
      6 * ((96482179 / 62500000000000000)) * ((92758117 / 250000000000000000)) * (126 / 100) + 8 * ((92758117 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12651 162) (d.f1 12651 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12651 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12651 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12651 162) (d.f1 12651 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12651 162) (d.w1 12651 162) (d.w2 12651 162)
  have hwexpr0 : 0 ≤ d.w0 12651 162 + d.w1 12651 162 * √(π / 2) +
      2 * d.w2 12651 162 + energyR16 12651 *
      radiusPolynomialRoot16 (d.w0 12651 162) (d.w1 12651 162) (d.w2 12651 162) := by
    positivity
  constructor
  · change (12651 : ℝ) ^ 8 * (mA 12651 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12651 162) (d.f1 12651 162) d.f2 + locationR16 12651 *
        radiusPolynomialRoot16 (d.f0 12651 162) (d.f1 12651 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12651 : ℝ) ^ 8 * (mA 12651 : ℝ) ^ 8 *
        ((((1156801851 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1156801851 / 250000000000000000)) * ((96482179 / 62500000000000000)) * (126 / 100) +
          2 * (((96482179 / 62500000000000000)) ^ 2 + 2 * ((1156801851 / 250000000000000000)) * ((92758117 / 250000000000000000))) +
          6 * ((96482179 / 62500000000000000)) * ((92758117 / 250000000000000000)) * (126 / 100) + 8 * ((92758117 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12651) *
          (32 * (((1156801851 / 250000000000000000) : ℝ) + (96482179 / 62500000000000000) + (92758117 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12651 : ℝ) ^ 16 *
      (d.w0 12651 162 + d.w1 12651 162 * √(π / 2) + 2 * d.w2 12651 162 +
        energyR16 12651 * radiusPolynomialRoot16 (d.w0 12651 162) (d.w1 12651 162)
          (d.w2 12651 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12651 : ℝ) ^ 16 *
        (((1854583909 / 100000000000000000000) : ℝ) + ((329875269 / 25000000000000000000)) * (126 / 100) + 2 * ((241056321 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12651) *
          (32 * (((1854583909 / 100000000000000000000) : ℝ) + (329875269 / 25000000000000000000) + (241056321 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12651

/-! A coarse bound on the actual paper statistics constant at dimension 12652. -/
namespace BstLean.Part266.Row12652
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12650 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12650 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12650 128 ≤ (12904 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12904 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12652) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12652 : ℕ))
    (by norm_num : (12652 : ℕ) ≤ 16384)
  have ht : paperTail256 12652 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12652 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12652 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12652 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12652 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12652 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12650 128 * √(2 / (12652 : ℝ)) *
      (√(12652 : ℝ) + paperT0 12652 + paperTail256 12652) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12652 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12652 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12652 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12650 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12650 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12652 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12652

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12652
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12652 (61 / 100) 162 (17 / (100 * 12652)) (26 / (10 * 12652)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12652 (61 / 100) 162 (17 / (100 * 12652)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (481993217 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (2381013 / 1562500000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5273947301 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12652 / 12652 * (61 / 100)) ^ 4 * inverseRadius8 (12652 - 1) /
            envelopeGap 12652 (61 / 100) 162 (17 / (100 * 12652)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12652

namespace BstLean.Part266.Row12652
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12652 162 ≤ (1156573387 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12652 162 ≤ (1543409939 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (370959167 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12652 162 ≤ (370828853 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12652 162 ≤ (1319188257 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12652 162 ≤ (240999163 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (481993217 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (481993217 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (2381013 / 1562500000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5273947301 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1832799 / 500000000) : ℝ) ≤ √(17 / (100 * 12652) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12652) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2195434393 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9759124961 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12652) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12652) ≤ (111777867 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12652) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12652 * (162 : ℝ) ^ 2 + 26 / (10 * 12652) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12652) : ℝ)) (tA 12652 * 162 ^ 2 + 26 / (10 * 12652)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1832799 / 500000000))) * ((481993217 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1832799 / 500000000)) ^ 3) * ((2381013 / 1562500000000000000000))) + ((5273947301 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1832799 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12652) : ℝ)) d.D d.V d.P (√(tA 12652) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1832799 / 500000000)) ^ 2 * (((2195434393 / 1000000000000000)) * ((9759124961 / 250000000000000000)))) + ((5273947301 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12652) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1832799 / 500000000)) * ((481993217 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12652) : ℝ)) (tA 12652 * 162 ^ 2 + 26 / (10 * 12652)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((481993217 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1832799 / 500000000)) ^ 2) * ((2381013 / 1562500000000000000000)) + ((5273947301 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12652) : ℝ)) (√(26 / (10 * 12652) : ℝ)) d.D d.V d.P (√(tA 12652) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1832799 / 500000000)) * (((2195434393 / 1000000000000000)) * ((9759124961 / 250000000000000000))) + ((5273947301 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12652) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((481993217 / 100000000000000000000) : ℝ) + ((5273947301 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12652

namespace BstLean.Part266.Row12652
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12652 162 ∧
    0 ≤ (tableEnvelope C).f1 12652 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12652 162 ∧
    0 ≤ (tableEnvelope C).w1 12652 162 ∧ 0 ≤ (tableEnvelope C).w2 12652 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12652 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12652 162 ∧ 0 ≤ d.f1 12652 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12652 162 ∧ 0 ≤ d.w1 12652 162 ∧ 0 ≤ d.w2 12652 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12652 ≤ 2 * (228 / 100 : ℝ) / 12652 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12652 ≤ 2 * (370 / 100 : ℝ) / 12652 := by
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
    (completeRAData (tableEnvelope C) 12652 162).locationBound 12652 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12652 162).energyBound 12652 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12652 162) (d.f1 12652 162) d.f2 ≤
      32 * (((1156573387 / 250000000000000000) : ℝ) + (1543409939 / 1000000000000000000) + (370959167 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12652 162) (d.w1 12652 162)
      (d.w2 12652 162) ≤
      32 * (((370828853 / 20000000000000000000) : ℝ) + (1319188257 / 100000000000000000000) + (240999163 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12652 162) (d.f1 12652 162) d.f2 ≤
      ((1156573387 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1156573387 / 250000000000000000)) * ((1543409939 / 1000000000000000000)) * (126 / 100) +
      2 * (((1543409939 / 1000000000000000000)) ^ 2 + 2 * ((1156573387 / 250000000000000000)) * ((370959167 / 1000000000000000000))) +
      6 * ((1543409939 / 1000000000000000000)) * ((370959167 / 1000000000000000000)) * (126 / 100) + 8 * ((370959167 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12652 162) (d.f1 12652 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12652 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12652 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12652 162) (d.f1 12652 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12652 162) (d.w1 12652 162) (d.w2 12652 162)
  have hwexpr0 : 0 ≤ d.w0 12652 162 + d.w1 12652 162 * √(π / 2) +
      2 * d.w2 12652 162 + energyR16 12652 *
      radiusPolynomialRoot16 (d.w0 12652 162) (d.w1 12652 162) (d.w2 12652 162) := by
    positivity
  constructor
  · change (12652 : ℝ) ^ 8 * (mA 12652 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12652 162) (d.f1 12652 162) d.f2 + locationR16 12652 *
        radiusPolynomialRoot16 (d.f0 12652 162) (d.f1 12652 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12652 : ℝ) ^ 8 * (mA 12652 : ℝ) ^ 8 *
        ((((1156573387 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1156573387 / 250000000000000000)) * ((1543409939 / 1000000000000000000)) * (126 / 100) +
          2 * (((1543409939 / 1000000000000000000)) ^ 2 + 2 * ((1156573387 / 250000000000000000)) * ((370959167 / 1000000000000000000))) +
          6 * ((1543409939 / 1000000000000000000)) * ((370959167 / 1000000000000000000)) * (126 / 100) + 8 * ((370959167 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12652) *
          (32 * (((1156573387 / 250000000000000000) : ℝ) + (1543409939 / 1000000000000000000) + (370959167 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12652 : ℝ) ^ 16 *
      (d.w0 12652 162 + d.w1 12652 162 * √(π / 2) + 2 * d.w2 12652 162 +
        energyR16 12652 * radiusPolynomialRoot16 (d.w0 12652 162) (d.w1 12652 162)
          (d.w2 12652 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12652 : ℝ) ^ 16 *
        (((370828853 / 20000000000000000000) : ℝ) + ((1319188257 / 100000000000000000000)) * (126 / 100) + 2 * ((240999163 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12652) *
          (32 * (((370828853 / 20000000000000000000) : ℝ) + (1319188257 / 100000000000000000000) + (240999163 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12652

/-! A coarse bound on the actual paper statistics constant at dimension 12653. -/
namespace BstLean.Part266.Row12653
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12651 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12651 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12651 128 ≤ (12905 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12905 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12653) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12653 : ℕ))
    (by norm_num : (12653 : ℕ) ≤ 16384)
  have ht : paperTail256 12653 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12653 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12653 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12653 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12653 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12653 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12651 128 * √(2 / (12653 : ℝ)) *
      (√(12653 : ℝ) + paperT0 12653 + paperTail256 12653) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12653 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12653 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12653 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12651 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12651 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12653 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12653

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12653
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12653 (61 / 100) 162 (17 / (100 * 12653)) (26 / (10 * 12653)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12653 (61 / 100) 162 (17 / (100 * 12653)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (24093947 / 5000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1523366623 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (26352907 / 5000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12653 / 12653 * (61 / 100)) ^ 4 * inverseRadius8 (12653 - 1) /
            envelopeGap 12653 (61 / 100) 162 (17 / (100 * 12653)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12653

namespace BstLean.Part266.Row12653
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12653 162 ≤ (2312690003 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12653 162 ≤ (1543105111 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (185442943 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12653 162 ≤ (1853704771 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12653 162 ≤ (65943777 / 5000000000000000000)
  w2 : (tableEnvelope C).w2 12653 162 ≤ (240942023 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (24093947 / 5000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (24093947 / 5000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1523366623 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (26352907 / 5000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3665453 / 1000000000) : ℝ) ≤ √(17 / (100 * 12653) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12653) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2195174117 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4878791191 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12653) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12653) ≤ (111769033 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12653) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12653 * (162 : ℝ) ^ 2 + 26 / (10 * 12653) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12653) : ℝ)) (tA 12653 * 162 ^ 2 + 26 / (10 * 12653)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3665453 / 1000000000))) * ((24093947 / 5000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3665453 / 1000000000)) ^ 3) * ((1523366623 / 1000000000000000000000000))) + ((26352907 / 5000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3665453 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12653) : ℝ)) d.D d.V d.P (√(tA 12653) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3665453 / 1000000000)) ^ 2 * (((2195174117 / 1000000000000000)) * ((4878791191 / 125000000000000000)))) + ((26352907 / 5000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12653) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3665453 / 1000000000)) * ((24093947 / 5000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12653) : ℝ)) (tA 12653 * 162 ^ 2 + 26 / (10 * 12653)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((24093947 / 5000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3665453 / 1000000000)) ^ 2) * ((1523366623 / 1000000000000000000000000)) + ((26352907 / 5000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12653) : ℝ)) (√(26 / (10 * 12653) : ℝ)) d.D d.V d.P (√(tA 12653) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3665453 / 1000000000)) * (((2195174117 / 1000000000000000)) * ((4878791191 / 125000000000000000))) + ((26352907 / 5000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12653) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((24093947 / 5000000000000000000) : ℝ) + ((26352907 / 5000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12653

namespace BstLean.Part266.Row12653
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12653 162 ∧
    0 ≤ (tableEnvelope C).f1 12653 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12653 162 ∧
    0 ≤ (tableEnvelope C).w1 12653 162 ∧ 0 ≤ (tableEnvelope C).w2 12653 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12653 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12653 162 ∧ 0 ≤ d.f1 12653 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12653 162 ∧ 0 ≤ d.w1 12653 162 ∧ 0 ≤ d.w2 12653 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12653 ≤ 2 * (228 / 100 : ℝ) / 12653 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12653 ≤ 2 * (370 / 100 : ℝ) / 12653 := by
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
    (completeRAData (tableEnvelope C) 12653 162).locationBound 12653 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12653 162).energyBound 12653 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12653 162) (d.f1 12653 162) d.f2 ≤
      32 * (((2312690003 / 500000000000000000) : ℝ) + (1543105111 / 1000000000000000000) + (185442943 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12653 162) (d.w1 12653 162)
      (d.w2 12653 162) ≤
      32 * (((1853704771 / 100000000000000000000) : ℝ) + (65943777 / 5000000000000000000) + (240942023 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12653 162) (d.f1 12653 162) d.f2 ≤
      ((2312690003 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2312690003 / 500000000000000000)) * ((1543105111 / 1000000000000000000)) * (126 / 100) +
      2 * (((1543105111 / 1000000000000000000)) ^ 2 + 2 * ((2312690003 / 500000000000000000)) * ((185442943 / 500000000000000000))) +
      6 * ((1543105111 / 1000000000000000000)) * ((185442943 / 500000000000000000)) * (126 / 100) + 8 * ((185442943 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12653 162) (d.f1 12653 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12653 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12653 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12653 162) (d.f1 12653 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12653 162) (d.w1 12653 162) (d.w2 12653 162)
  have hwexpr0 : 0 ≤ d.w0 12653 162 + d.w1 12653 162 * √(π / 2) +
      2 * d.w2 12653 162 + energyR16 12653 *
      radiusPolynomialRoot16 (d.w0 12653 162) (d.w1 12653 162) (d.w2 12653 162) := by
    positivity
  constructor
  · change (12653 : ℝ) ^ 8 * (mA 12653 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12653 162) (d.f1 12653 162) d.f2 + locationR16 12653 *
        radiusPolynomialRoot16 (d.f0 12653 162) (d.f1 12653 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12653 : ℝ) ^ 8 * (mA 12653 : ℝ) ^ 8 *
        ((((2312690003 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2312690003 / 500000000000000000)) * ((1543105111 / 1000000000000000000)) * (126 / 100) +
          2 * (((1543105111 / 1000000000000000000)) ^ 2 + 2 * ((2312690003 / 500000000000000000)) * ((185442943 / 500000000000000000))) +
          6 * ((1543105111 / 1000000000000000000)) * ((185442943 / 500000000000000000)) * (126 / 100) + 8 * ((185442943 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12653) *
          (32 * (((2312690003 / 500000000000000000) : ℝ) + (1543105111 / 1000000000000000000) + (185442943 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12653 : ℝ) ^ 16 *
      (d.w0 12653 162 + d.w1 12653 162 * √(π / 2) + 2 * d.w2 12653 162 +
        energyR16 12653 * radiusPolynomialRoot16 (d.w0 12653 162) (d.w1 12653 162)
          (d.w2 12653 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12653 : ℝ) ^ 16 *
        (((1853704771 / 100000000000000000000) : ℝ) + ((65943777 / 5000000000000000000)) * (126 / 100) + 2 * ((240942023 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12653) *
          (32 * (((1853704771 / 100000000000000000000) : ℝ) + (65943777 / 5000000000000000000) + (240942023 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12653

/-! A coarse bound on the actual paper statistics constant at dimension 12654. -/
namespace BstLean.Part266.Row12654
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12652 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12652 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12652 128 ≤ (12906 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12906 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12654) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12654 : ℕ))
    (by norm_num : (12654 : ℕ) ≤ 16384)
  have ht : paperTail256 12654 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12654 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12654 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12654 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12654 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12654 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12652 128 * √(2 / (12654 : ℝ)) *
      (√(12654 : ℝ) + paperT0 12654 + paperTail256 12654) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12654 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12654 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12654 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12652 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12652 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12654 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12654

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12654
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12654 (61 / 100) 162 (17 / (100 * 12654)) (26 / (10 * 12654)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12654 (61 / 100) 162 (17 / (100 * 12654)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (481764699 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (380721279 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2633608959 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12654 / 12654 * (61 / 100)) ^ 4 * inverseRadius8 (12654 - 1) /
            envelopeGap 12654 (61 / 100) 162 (17 / (100 * 12654)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12654

namespace BstLean.Part266.Row12654
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12654 162 ≤ (2312233389 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12654 162 ≤ (1542800381 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (92703157 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12654 162 ≤ (1853265429 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12654 162 ≤ (1318562927 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12654 162 ≤ (240884901 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (481764699 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (481764699 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (380721279 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2633608959 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((916327 / 250000000) : ℝ) ≤ √(17 / (100 * 12654) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12654) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (548728473 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39024160671 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12654) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12654) ≤ (558801 / 5000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12654) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12654 * (162 : ℝ) ^ 2 + 26 / (10 * 12654) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12654) : ℝ)) (tA 12654 * 162 ^ 2 + 26 / (10 * 12654)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((916327 / 250000000))) * ((481764699 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((916327 / 250000000)) ^ 3) * ((380721279 / 250000000000000000000000))) + ((2633608959 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((916327 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12654) : ℝ)) d.D d.V d.P (√(tA 12654) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((916327 / 250000000)) ^ 2 * (((548728473 / 250000000000000)) * ((39024160671 / 1000000000000000000)))) + ((2633608959 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12654) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((916327 / 250000000)) * ((481764699 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12654) : ℝ)) (tA 12654 * 162 ^ 2 + 26 / (10 * 12654)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((481764699 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((916327 / 250000000)) ^ 2) * ((380721279 / 250000000000000000000000)) + ((2633608959 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12654) : ℝ)) (√(26 / (10 * 12654) : ℝ)) d.D d.V d.P (√(tA 12654) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((916327 / 250000000)) * (((548728473 / 250000000000000)) * ((39024160671 / 1000000000000000000))) + ((2633608959 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12654) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((481764699 / 100000000000000000000) : ℝ) + ((2633608959 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12654

namespace BstLean.Part266.Row12654
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12654 162 ∧
    0 ≤ (tableEnvelope C).f1 12654 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12654 162 ∧
    0 ≤ (tableEnvelope C).w1 12654 162 ∧ 0 ≤ (tableEnvelope C).w2 12654 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12654 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12654 162 ∧ 0 ≤ d.f1 12654 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12654 162 ∧ 0 ≤ d.w1 12654 162 ∧ 0 ≤ d.w2 12654 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12654 ≤ 2 * (228 / 100 : ℝ) / 12654 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12654 ≤ 2 * (370 / 100 : ℝ) / 12654 := by
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
    (completeRAData (tableEnvelope C) 12654 162).locationBound 12654 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12654 162).energyBound 12654 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12654 162) (d.f1 12654 162) d.f2 ≤
      32 * (((2312233389 / 500000000000000000) : ℝ) + (1542800381 / 1000000000000000000) + (92703157 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12654 162) (d.w1 12654 162)
      (d.w2 12654 162) ≤
      32 * (((1853265429 / 100000000000000000000) : ℝ) + (1318562927 / 100000000000000000000) + (240884901 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12654 162) (d.f1 12654 162) d.f2 ≤
      ((2312233389 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2312233389 / 500000000000000000)) * ((1542800381 / 1000000000000000000)) * (126 / 100) +
      2 * (((1542800381 / 1000000000000000000)) ^ 2 + 2 * ((2312233389 / 500000000000000000)) * ((92703157 / 250000000000000000))) +
      6 * ((1542800381 / 1000000000000000000)) * ((92703157 / 250000000000000000)) * (126 / 100) + 8 * ((92703157 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12654 162) (d.f1 12654 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12654 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12654 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12654 162) (d.f1 12654 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12654 162) (d.w1 12654 162) (d.w2 12654 162)
  have hwexpr0 : 0 ≤ d.w0 12654 162 + d.w1 12654 162 * √(π / 2) +
      2 * d.w2 12654 162 + energyR16 12654 *
      radiusPolynomialRoot16 (d.w0 12654 162) (d.w1 12654 162) (d.w2 12654 162) := by
    positivity
  constructor
  · change (12654 : ℝ) ^ 8 * (mA 12654 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12654 162) (d.f1 12654 162) d.f2 + locationR16 12654 *
        radiusPolynomialRoot16 (d.f0 12654 162) (d.f1 12654 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12654 : ℝ) ^ 8 * (mA 12654 : ℝ) ^ 8 *
        ((((2312233389 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2312233389 / 500000000000000000)) * ((1542800381 / 1000000000000000000)) * (126 / 100) +
          2 * (((1542800381 / 1000000000000000000)) ^ 2 + 2 * ((2312233389 / 500000000000000000)) * ((92703157 / 250000000000000000))) +
          6 * ((1542800381 / 1000000000000000000)) * ((92703157 / 250000000000000000)) * (126 / 100) + 8 * ((92703157 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12654) *
          (32 * (((2312233389 / 500000000000000000) : ℝ) + (1542800381 / 1000000000000000000) + (92703157 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12654 : ℝ) ^ 16 *
      (d.w0 12654 162 + d.w1 12654 162 * √(π / 2) + 2 * d.w2 12654 162 +
        energyR16 12654 * radiusPolynomialRoot16 (d.w0 12654 162) (d.w1 12654 162)
          (d.w2 12654 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12654 : ℝ) ^ 16 *
        (((1853265429 / 100000000000000000000) : ℝ) + ((1318562927 / 100000000000000000000)) * (126 / 100) + 2 * ((240884901 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12654) *
          (32 * (((1853265429 / 100000000000000000000) : ℝ) + (1318562927 / 100000000000000000000) + (240884901 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12654

/-! A coarse bound on the actual paper statistics constant at dimension 12655. -/
namespace BstLean.Part266.Row12655
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12653 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12653 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12653 128 ≤ (12907 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12907 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12655) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12655 : ℕ))
    (by norm_num : (12655 : ℕ) ≤ 16384)
  have ht : paperTail256 12655 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12655 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12655 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12655 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12655 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12655 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12653 128 * √(2 / (12655 : ℝ)) *
      (√(12655 : ℝ) + paperT0 12655 + paperTail256 12655) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12655 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12655 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12655 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12653 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12653 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12655 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12655

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12655
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12655 (61 / 100) 162 (17 / (100 * 12655)) (26 / (10 * 12655)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12655 (61 / 100) 162 (17 / (100 * 12655)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (96330099 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (7612019 / 5000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1315964213 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12655 / 12655 * (61 / 100)) ^ 4 * inverseRadius8 (12655 - 1) /
            envelopeGap 12655 (61 / 100) 162 (17 / (100 * 12655)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12655

namespace BstLean.Part266.Row12655
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12655 162 ≤ (1155888467 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12655 162 ≤ (1542495751 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (5792803 / 15625000000000000)
  w0 : (tableEnvelope C).w0 12655 162 ≤ (2895041 / 156250000000000000)
  w1 : (tableEnvelope C).w1 12655 162 ≤ (1318250421 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12655 162 ≤ (96331119 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (96330099 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (96330099 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (7612019 / 5000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1315964213 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3665163 / 1000000000) : ℝ) ≤ √(17 / (100 * 12655) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12655) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (54866343 / 25000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19508996643 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12655) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12655) ≤ (111751369 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12655) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12655 * (162 : ℝ) ^ 2 + 26 / (10 * 12655) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12655) : ℝ)) (tA 12655 * 162 ^ 2 + 26 / (10 * 12655)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3665163 / 1000000000))) * ((96330099 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3665163 / 1000000000)) ^ 3) * ((7612019 / 5000000000000000000000))) + ((1315964213 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3665163 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12655) : ℝ)) d.D d.V d.P (√(tA 12655) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3665163 / 1000000000)) ^ 2 * (((54866343 / 25000000000000)) * ((19508996643 / 500000000000000000)))) + ((1315964213 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12655) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3665163 / 1000000000)) * ((96330099 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12655) : ℝ)) (tA 12655 * 162 ^ 2 + 26 / (10 * 12655)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((96330099 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3665163 / 1000000000)) ^ 2) * ((7612019 / 5000000000000000000000)) + ((1315964213 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12655) : ℝ)) (√(26 / (10 * 12655) : ℝ)) d.D d.V d.P (√(tA 12655) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3665163 / 1000000000)) * (((54866343 / 25000000000000)) * ((19508996643 / 500000000000000000))) + ((1315964213 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12655) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((96330099 / 20000000000000000000) : ℝ) + ((1315964213 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12655

namespace BstLean.Part266.Row12655
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12655 162 ∧
    0 ≤ (tableEnvelope C).f1 12655 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12655 162 ∧
    0 ≤ (tableEnvelope C).w1 12655 162 ∧ 0 ≤ (tableEnvelope C).w2 12655 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12655 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12655 162 ∧ 0 ≤ d.f1 12655 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12655 162 ∧ 0 ≤ d.w1 12655 162 ∧ 0 ≤ d.w2 12655 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12655 ≤ 2 * (228 / 100 : ℝ) / 12655 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12655 ≤ 2 * (370 / 100 : ℝ) / 12655 := by
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
    (completeRAData (tableEnvelope C) 12655 162).locationBound 12655 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12655 162).energyBound 12655 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12655 162) (d.f1 12655 162) d.f2 ≤
      32 * (((1155888467 / 250000000000000000) : ℝ) + (1542495751 / 1000000000000000000) + (5792803 / 15625000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12655 162) (d.w1 12655 162)
      (d.w2 12655 162) ≤
      32 * (((2895041 / 156250000000000000) : ℝ) + (1318250421 / 100000000000000000000) + (96331119 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12655 162) (d.f1 12655 162) d.f2 ≤
      ((1155888467 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1155888467 / 250000000000000000)) * ((1542495751 / 1000000000000000000)) * (126 / 100) +
      2 * (((1542495751 / 1000000000000000000)) ^ 2 + 2 * ((1155888467 / 250000000000000000)) * ((5792803 / 15625000000000000))) +
      6 * ((1542495751 / 1000000000000000000)) * ((5792803 / 15625000000000000)) * (126 / 100) + 8 * ((5792803 / 15625000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12655 162) (d.f1 12655 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12655 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12655 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12655 162) (d.f1 12655 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12655 162) (d.w1 12655 162) (d.w2 12655 162)
  have hwexpr0 : 0 ≤ d.w0 12655 162 + d.w1 12655 162 * √(π / 2) +
      2 * d.w2 12655 162 + energyR16 12655 *
      radiusPolynomialRoot16 (d.w0 12655 162) (d.w1 12655 162) (d.w2 12655 162) := by
    positivity
  constructor
  · change (12655 : ℝ) ^ 8 * (mA 12655 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12655 162) (d.f1 12655 162) d.f2 + locationR16 12655 *
        radiusPolynomialRoot16 (d.f0 12655 162) (d.f1 12655 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12655 : ℝ) ^ 8 * (mA 12655 : ℝ) ^ 8 *
        ((((1155888467 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1155888467 / 250000000000000000)) * ((1542495751 / 1000000000000000000)) * (126 / 100) +
          2 * (((1542495751 / 1000000000000000000)) ^ 2 + 2 * ((1155888467 / 250000000000000000)) * ((5792803 / 15625000000000000))) +
          6 * ((1542495751 / 1000000000000000000)) * ((5792803 / 15625000000000000)) * (126 / 100) + 8 * ((5792803 / 15625000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12655) *
          (32 * (((1155888467 / 250000000000000000) : ℝ) + (1542495751 / 1000000000000000000) + (5792803 / 15625000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12655 : ℝ) ^ 16 *
      (d.w0 12655 162 + d.w1 12655 162 * √(π / 2) + 2 * d.w2 12655 162 +
        energyR16 12655 * radiusPolynomialRoot16 (d.w0 12655 162) (d.w1 12655 162)
          (d.w2 12655 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12655 : ℝ) ^ 16 *
        (((2895041 / 156250000000000000) : ℝ) + ((1318250421 / 100000000000000000000)) * (126 / 100) + 2 * ((96331119 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12655) *
          (32 * (((2895041 / 156250000000000000) : ℝ) + (1318250421 / 100000000000000000000) + (96331119 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12655

/-! A coarse bound on the actual paper statistics constant at dimension 12656. -/
namespace BstLean.Part266.Row12656
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12654 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12654 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12654 128 ≤ (12908 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12908 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12656) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12656 : ℕ))
    (by norm_num : (12656 : ℕ) ≤ 16384)
  have ht : paperTail256 12656 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12656 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12656 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12656 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12656 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12656 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12654 128 * √(2 / (12656 : ℝ)) *
      (√(12656 : ℝ) + paperT0 12656 + paperTail256 12656) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12656 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12656 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12656 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12654 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12654 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12656 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12656

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12656
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12656 (61 / 100) 162 (17 / (100 * 12656)) (26 / (10 * 12656)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12656 (61 / 100) 162 (17 / (100 * 12656)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (481536327 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1521922673 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2630249101 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12656 / 12656 * (61 / 100)) ^ 4 * inverseRadius8 (12656 - 1) /
            envelopeGap 12656 (61 / 100) 162 (17 / (100 * 12656)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12656

namespace BstLean.Part266.Row12656
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12656 162 ≤ (4622641269 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12656 162 ≤ (1542191219 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (185333089 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12656 162 ≤ (1852387201 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12656 162 ≤ (65896901 / 5000000000000000000)
  w2 : (tableEnvelope C).w2 12656 162 ≤ (481541423 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (481536327 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (481536327 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1521922673 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2630249101 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1832509 / 500000000) : ℝ) ≤ √(17 / (100 * 12656) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12656) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (171437 / 78125000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9752956837 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12656) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12656) ≤ (111742539 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12656) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12656 * (162 : ℝ) ^ 2 + 26 / (10 * 12656) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12656) : ℝ)) (tA 12656 * 162 ^ 2 + 26 / (10 * 12656)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1832509 / 500000000))) * ((481536327 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1832509 / 500000000)) ^ 3) * ((1521922673 / 1000000000000000000000000))) + ((2630249101 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1832509 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12656) : ℝ)) d.D d.V d.P (√(tA 12656) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1832509 / 500000000)) ^ 2 * (((171437 / 78125000000)) * ((9752956837 / 250000000000000000)))) + ((2630249101 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12656) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1832509 / 500000000)) * ((481536327 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12656) : ℝ)) (tA 12656 * 162 ^ 2 + 26 / (10 * 12656)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((481536327 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1832509 / 500000000)) ^ 2) * ((1521922673 / 1000000000000000000000000)) + ((2630249101 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12656) : ℝ)) (√(26 / (10 * 12656) : ℝ)) d.D d.V d.P (√(tA 12656) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1832509 / 500000000)) * (((171437 / 78125000000)) * ((9752956837 / 250000000000000000))) + ((2630249101 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12656) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((481536327 / 100000000000000000000) : ℝ) + ((2630249101 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12656

namespace BstLean.Part266.Row12656
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12656 162 ∧
    0 ≤ (tableEnvelope C).f1 12656 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12656 162 ∧
    0 ≤ (tableEnvelope C).w1 12656 162 ∧ 0 ≤ (tableEnvelope C).w2 12656 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12656 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12656 162 ∧ 0 ≤ d.f1 12656 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12656 162 ∧ 0 ≤ d.w1 12656 162 ∧ 0 ≤ d.w2 12656 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12656 ≤ 2 * (228 / 100 : ℝ) / 12656 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12656 ≤ 2 * (370 / 100 : ℝ) / 12656 := by
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
    (completeRAData (tableEnvelope C) 12656 162).locationBound 12656 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12656 162).energyBound 12656 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12656 162) (d.f1 12656 162) d.f2 ≤
      32 * (((4622641269 / 1000000000000000000) : ℝ) + (1542191219 / 1000000000000000000) + (185333089 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12656 162) (d.w1 12656 162)
      (d.w2 12656 162) ≤
      32 * (((1852387201 / 100000000000000000000) : ℝ) + (65896901 / 5000000000000000000) + (481541423 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12656 162) (d.f1 12656 162) d.f2 ≤
      ((4622641269 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4622641269 / 1000000000000000000)) * ((1542191219 / 1000000000000000000)) * (126 / 100) +
      2 * (((1542191219 / 1000000000000000000)) ^ 2 + 2 * ((4622641269 / 1000000000000000000)) * ((185333089 / 500000000000000000))) +
      6 * ((1542191219 / 1000000000000000000)) * ((185333089 / 500000000000000000)) * (126 / 100) + 8 * ((185333089 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12656 162) (d.f1 12656 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12656 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12656 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12656 162) (d.f1 12656 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12656 162) (d.w1 12656 162) (d.w2 12656 162)
  have hwexpr0 : 0 ≤ d.w0 12656 162 + d.w1 12656 162 * √(π / 2) +
      2 * d.w2 12656 162 + energyR16 12656 *
      radiusPolynomialRoot16 (d.w0 12656 162) (d.w1 12656 162) (d.w2 12656 162) := by
    positivity
  constructor
  · change (12656 : ℝ) ^ 8 * (mA 12656 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12656 162) (d.f1 12656 162) d.f2 + locationR16 12656 *
        radiusPolynomialRoot16 (d.f0 12656 162) (d.f1 12656 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12656 : ℝ) ^ 8 * (mA 12656 : ℝ) ^ 8 *
        ((((4622641269 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4622641269 / 1000000000000000000)) * ((1542191219 / 1000000000000000000)) * (126 / 100) +
          2 * (((1542191219 / 1000000000000000000)) ^ 2 + 2 * ((4622641269 / 1000000000000000000)) * ((185333089 / 500000000000000000))) +
          6 * ((1542191219 / 1000000000000000000)) * ((185333089 / 500000000000000000)) * (126 / 100) + 8 * ((185333089 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12656) *
          (32 * (((4622641269 / 1000000000000000000) : ℝ) + (1542191219 / 1000000000000000000) + (185333089 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12656 : ℝ) ^ 16 *
      (d.w0 12656 162 + d.w1 12656 162 * √(π / 2) + 2 * d.w2 12656 162 +
        energyR16 12656 * radiusPolynomialRoot16 (d.w0 12656 162) (d.w1 12656 162)
          (d.w2 12656 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12656 : ℝ) ^ 16 *
        (((1852387201 / 100000000000000000000) : ℝ) + ((65896901 / 5000000000000000000)) * (126 / 100) + 2 * ((481541423 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12656) *
          (32 * (((1852387201 / 100000000000000000000) : ℝ) + (65896901 / 5000000000000000000) + (481541423 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12656

/-! A coarse bound on the actual paper statistics constant at dimension 12657. -/
namespace BstLean.Part266.Row12657
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12655 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12655 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12655 128 ≤ (12909 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12909 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12657) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12657 : ℕ))
    (by norm_num : (12657 : ℕ) ≤ 16384)
  have ht : paperTail256 12657 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12657 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12657 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12657 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12657 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12657 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12655 128 * √(2 / (12657 : ℝ)) *
      (√(12657 : ℝ) + paperT0 12657 + paperTail256 12657) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12657 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12657 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12657 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12655 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12655 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12657 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12657

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12657
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12657 (61 / 100) 162 (17 / (100 * 12657)) (26 / (10 * 12657)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12657 (61 / 100) 162 (17 / (100 * 12657)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (96284439 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1521441737 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1051428393 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12657 / 12657 * (61 / 100)) ^ 4 * inverseRadius8 (12657 - 1) /
            envelopeGap 12657 (61 / 100) 162 (17 / (100 * 12657)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12657

namespace BstLean.Part266.Row12657
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12657 162 ≤ (1155431337 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12657 162 ≤ (308377189 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (92648221 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12657 162 ≤ (1851947567 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12657 162 ≤ (263525073 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12657 162 ≤ (60178411 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (96284439 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (96284439 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1521441737 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1051428393 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1832437 / 500000000) : ℝ) ≤ √(17 / (100 * 12657) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12657) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2194133531 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9751415721 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12657) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12657) ≤ (11173371 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12657) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12657 * (162 : ℝ) ^ 2 + 26 / (10 * 12657) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12657) : ℝ)) (tA 12657 * 162 ^ 2 + 26 / (10 * 12657)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1832437 / 500000000))) * ((96284439 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1832437 / 500000000)) ^ 3) * ((1521441737 / 1000000000000000000000000))) + ((1051428393 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1832437 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12657) : ℝ)) d.D d.V d.P (√(tA 12657) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1832437 / 500000000)) ^ 2 * (((2194133531 / 1000000000000000)) * ((9751415721 / 250000000000000000)))) + ((1051428393 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12657) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1832437 / 500000000)) * ((96284439 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12657) : ℝ)) (tA 12657 * 162 ^ 2 + 26 / (10 * 12657)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((96284439 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1832437 / 500000000)) ^ 2) * ((1521441737 / 1000000000000000000000000)) + ((1051428393 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12657) : ℝ)) (√(26 / (10 * 12657) : ℝ)) d.D d.V d.P (√(tA 12657) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1832437 / 500000000)) * (((2194133531 / 1000000000000000)) * ((9751415721 / 250000000000000000))) + ((1051428393 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12657) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((96284439 / 20000000000000000000) : ℝ) + ((1051428393 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12657

namespace BstLean.Part266.Row12657
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12657 162 ∧
    0 ≤ (tableEnvelope C).f1 12657 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12657 162 ∧
    0 ≤ (tableEnvelope C).w1 12657 162 ∧ 0 ≤ (tableEnvelope C).w2 12657 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12657 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12657 162 ∧ 0 ≤ d.f1 12657 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12657 162 ∧ 0 ≤ d.w1 12657 162 ∧ 0 ≤ d.w2 12657 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12657 ≤ 2 * (228 / 100 : ℝ) / 12657 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12657 ≤ 2 * (370 / 100 : ℝ) / 12657 := by
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
    (completeRAData (tableEnvelope C) 12657 162).locationBound 12657 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12657 162).energyBound 12657 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12657 162) (d.f1 12657 162) d.f2 ≤
      32 * (((1155431337 / 250000000000000000) : ℝ) + (308377189 / 200000000000000000) + (92648221 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12657 162) (d.w1 12657 162)
      (d.w2 12657 162) ≤
      32 * (((1851947567 / 100000000000000000000) : ℝ) + (263525073 / 20000000000000000000) + (60178411 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12657 162) (d.f1 12657 162) d.f2 ≤
      ((1155431337 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1155431337 / 250000000000000000)) * ((308377189 / 200000000000000000)) * (126 / 100) +
      2 * (((308377189 / 200000000000000000)) ^ 2 + 2 * ((1155431337 / 250000000000000000)) * ((92648221 / 250000000000000000))) +
      6 * ((308377189 / 200000000000000000)) * ((92648221 / 250000000000000000)) * (126 / 100) + 8 * ((92648221 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12657 162) (d.f1 12657 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12657 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12657 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12657 162) (d.f1 12657 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12657 162) (d.w1 12657 162) (d.w2 12657 162)
  have hwexpr0 : 0 ≤ d.w0 12657 162 + d.w1 12657 162 * √(π / 2) +
      2 * d.w2 12657 162 + energyR16 12657 *
      radiusPolynomialRoot16 (d.w0 12657 162) (d.w1 12657 162) (d.w2 12657 162) := by
    positivity
  constructor
  · change (12657 : ℝ) ^ 8 * (mA 12657 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12657 162) (d.f1 12657 162) d.f2 + locationR16 12657 *
        radiusPolynomialRoot16 (d.f0 12657 162) (d.f1 12657 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12657 : ℝ) ^ 8 * (mA 12657 : ℝ) ^ 8 *
        ((((1155431337 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1155431337 / 250000000000000000)) * ((308377189 / 200000000000000000)) * (126 / 100) +
          2 * (((308377189 / 200000000000000000)) ^ 2 + 2 * ((1155431337 / 250000000000000000)) * ((92648221 / 250000000000000000))) +
          6 * ((308377189 / 200000000000000000)) * ((92648221 / 250000000000000000)) * (126 / 100) + 8 * ((92648221 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12657) *
          (32 * (((1155431337 / 250000000000000000) : ℝ) + (308377189 / 200000000000000000) + (92648221 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12657 : ℝ) ^ 16 *
      (d.w0 12657 162 + d.w1 12657 162 * √(π / 2) + 2 * d.w2 12657 162 +
        energyR16 12657 * radiusPolynomialRoot16 (d.w0 12657 162) (d.w1 12657 162)
          (d.w2 12657 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12657 : ℝ) ^ 16 *
        (((1851947567 / 100000000000000000000) : ℝ) + ((263525073 / 20000000000000000000)) * (126 / 100) + 2 * ((60178411 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12657) *
          (32 * (((1851947567 / 100000000000000000000) : ℝ) + (263525073 / 20000000000000000000) + (60178411 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12657

/-! A coarse bound on the actual paper statistics constant at dimension 12658. -/
namespace BstLean.Part266.Row12658
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12656 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12656 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12656 128 ≤ (12910 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12910 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12658) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12658 : ℕ))
    (by norm_num : (12658 : ℕ) ≤ 16384)
  have ht : paperTail256 12658 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12658 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12658 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12658 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12658 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12658 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12656 128 * √(2 / (12658 : ℝ)) *
      (√(12658 : ℝ) + paperT0 12658 + paperTail256 12658) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12658 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12658 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12658 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12656 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12656 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12658 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12658

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12658
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12658 (61 / 100) 162 (17 / (100 * 12658)) (26 / (10 * 12658)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12658 (61 / 100) 162 (17 / (100 * 12658)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (481308099 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1520960991 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5253788139 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12658 / 12658 * (61 / 100)) ^ 4 * inverseRadius8 (12658 - 1) /
            envelopeGap 12658 (61 / 100) 162 (17 / (100 * 12658)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12658

namespace BstLean.Part266.Row12658
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12658 162 ≤ (2310406691 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12658 162 ≤ (1541581611 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (185259857 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12658 162 ≤ (1851508833 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12658 162 ≤ (1317313173 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12658 162 ≤ (481313189 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (481308099 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (481308099 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1520960991 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5253788139 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3664729 / 1000000000) : ℝ) ≤ √(17 / (100 * 12658) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12658) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2193873513 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19499749941 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12658) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12658) ≤ (111724883 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12658) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12658 * (162 : ℝ) ^ 2 + 26 / (10 * 12658) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12658) : ℝ)) (tA 12658 * 162 ^ 2 + 26 / (10 * 12658)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3664729 / 1000000000))) * ((481308099 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3664729 / 1000000000)) ^ 3) * ((1520960991 / 1000000000000000000000000))) + ((5253788139 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3664729 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12658) : ℝ)) d.D d.V d.P (√(tA 12658) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3664729 / 1000000000)) ^ 2 * (((2193873513 / 1000000000000000)) * ((19499749941 / 500000000000000000)))) + ((5253788139 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12658) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3664729 / 1000000000)) * ((481308099 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12658) : ℝ)) (tA 12658 * 162 ^ 2 + 26 / (10 * 12658)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((481308099 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3664729 / 1000000000)) ^ 2) * ((1520960991 / 1000000000000000000000000)) + ((5253788139 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12658) : ℝ)) (√(26 / (10 * 12658) : ℝ)) d.D d.V d.P (√(tA 12658) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3664729 / 1000000000)) * (((2193873513 / 1000000000000000)) * ((19499749941 / 500000000000000000))) + ((5253788139 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12658) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((481308099 / 100000000000000000000) : ℝ) + ((5253788139 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12658

namespace BstLean.Part266.Row12658
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12658 162 ∧
    0 ≤ (tableEnvelope C).f1 12658 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12658 162 ∧
    0 ≤ (tableEnvelope C).w1 12658 162 ∧ 0 ≤ (tableEnvelope C).w2 12658 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12658 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12658 162 ∧ 0 ≤ d.f1 12658 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12658 162 ∧ 0 ≤ d.w1 12658 162 ∧ 0 ≤ d.w2 12658 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12658 ≤ 2 * (228 / 100 : ℝ) / 12658 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12658 ≤ 2 * (370 / 100 : ℝ) / 12658 := by
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
    (completeRAData (tableEnvelope C) 12658 162).locationBound 12658 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12658 162).energyBound 12658 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12658 162) (d.f1 12658 162) d.f2 ≤
      32 * (((2310406691 / 500000000000000000) : ℝ) + (1541581611 / 1000000000000000000) + (185259857 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12658 162) (d.w1 12658 162)
      (d.w2 12658 162) ≤
      32 * (((1851508833 / 100000000000000000000) : ℝ) + (1317313173 / 100000000000000000000) + (481313189 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12658 162) (d.f1 12658 162) d.f2 ≤
      ((2310406691 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2310406691 / 500000000000000000)) * ((1541581611 / 1000000000000000000)) * (126 / 100) +
      2 * (((1541581611 / 1000000000000000000)) ^ 2 + 2 * ((2310406691 / 500000000000000000)) * ((185259857 / 500000000000000000))) +
      6 * ((1541581611 / 1000000000000000000)) * ((185259857 / 500000000000000000)) * (126 / 100) + 8 * ((185259857 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12658 162) (d.f1 12658 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12658 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12658 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12658 162) (d.f1 12658 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12658 162) (d.w1 12658 162) (d.w2 12658 162)
  have hwexpr0 : 0 ≤ d.w0 12658 162 + d.w1 12658 162 * √(π / 2) +
      2 * d.w2 12658 162 + energyR16 12658 *
      radiusPolynomialRoot16 (d.w0 12658 162) (d.w1 12658 162) (d.w2 12658 162) := by
    positivity
  constructor
  · change (12658 : ℝ) ^ 8 * (mA 12658 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12658 162) (d.f1 12658 162) d.f2 + locationR16 12658 *
        radiusPolynomialRoot16 (d.f0 12658 162) (d.f1 12658 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12658 : ℝ) ^ 8 * (mA 12658 : ℝ) ^ 8 *
        ((((2310406691 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2310406691 / 500000000000000000)) * ((1541581611 / 1000000000000000000)) * (126 / 100) +
          2 * (((1541581611 / 1000000000000000000)) ^ 2 + 2 * ((2310406691 / 500000000000000000)) * ((185259857 / 500000000000000000))) +
          6 * ((1541581611 / 1000000000000000000)) * ((185259857 / 500000000000000000)) * (126 / 100) + 8 * ((185259857 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12658) *
          (32 * (((2310406691 / 500000000000000000) : ℝ) + (1541581611 / 1000000000000000000) + (185259857 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12658 : ℝ) ^ 16 *
      (d.w0 12658 162 + d.w1 12658 162 * √(π / 2) + 2 * d.w2 12658 162 +
        energyR16 12658 * radiusPolynomialRoot16 (d.w0 12658 162) (d.w1 12658 162)
          (d.w2 12658 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12658 : ℝ) ^ 16 *
        (((1851508833 / 100000000000000000000) : ℝ) + ((1317313173 / 100000000000000000000)) * (126 / 100) + 2 * ((481313189 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12658) *
          (32 * (((1851508833 / 100000000000000000000) : ℝ) + (1317313173 / 100000000000000000000) + (481313189 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12658

/-! A coarse bound on the actual paper statistics constant at dimension 12659. -/
namespace BstLean.Part266.Row12659
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12657 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12657 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12657 128 ≤ (12911 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12911 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12659) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12659 : ℕ))
    (by norm_num : (12659 : ℕ) ≤ 16384)
  have ht : paperTail256 12659 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12659 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12659 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12659 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12659 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12659 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12657 128 * √(2 / (12659 : ℝ)) *
      (√(12659 : ℝ) + paperT0 12659 + paperTail256 12659) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12659 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12659 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12659 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12657 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12657 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12659 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12659

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12659
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12659 (61 / 100) 162 (17 / (100 * 12659)) (26 / (10 * 12659)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12659 (61 / 100) 162 (17 / (100 * 12659)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (481194039 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (304096087 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2625218361 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12659 / 12659 * (61 / 100)) ^ 4 * inverseRadius8 (12659 - 1) /
            envelopeGap 12659 (61 / 100) 162 (17 / (100 * 12659)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12659

namespace BstLean.Part266.Row12659
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12659 162 ≤ (4619901731 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12659 162 ≤ (24082459 / 15625000000000000)
  f2 : (tableEnvelope C).f2 ≤ (185223283 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12659 162 ≤ (7404281 / 400000000000000000)
  w1 : (tableEnvelope C).w1 12659 162 ≤ (1317001087 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12659 162 ≤ (240599563 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (481194039 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (481194039 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (304096087 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2625218361 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((458073 / 125000000) : ℝ) ≤ √(17 / (100 * 12659) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12659) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2193613547 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19496669171 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12659) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12659) ≤ (111716057 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12659) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12659 * (162 : ℝ) ^ 2 + 26 / (10 * 12659) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12659) : ℝ)) (tA 12659 * 162 ^ 2 + 26 / (10 * 12659)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((458073 / 125000000))) * ((481194039 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((458073 / 125000000)) ^ 3) * ((304096087 / 200000000000000000000000))) + ((2625218361 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((458073 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12659) : ℝ)) d.D d.V d.P (√(tA 12659) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((458073 / 125000000)) ^ 2 * (((2193613547 / 1000000000000000)) * ((19496669171 / 500000000000000000)))) + ((2625218361 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12659) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((458073 / 125000000)) * ((481194039 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12659) : ℝ)) (tA 12659 * 162 ^ 2 + 26 / (10 * 12659)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((481194039 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((458073 / 125000000)) ^ 2) * ((304096087 / 200000000000000000000000)) + ((2625218361 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12659) : ℝ)) (√(26 / (10 * 12659) : ℝ)) d.D d.V d.P (√(tA 12659) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((458073 / 125000000)) * (((2193613547 / 1000000000000000)) * ((19496669171 / 500000000000000000))) + ((2625218361 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12659) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((481194039 / 100000000000000000000) : ℝ) + ((2625218361 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12659

namespace BstLean.Part266.Row12659
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12659 162 ∧
    0 ≤ (tableEnvelope C).f1 12659 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12659 162 ∧
    0 ≤ (tableEnvelope C).w1 12659 162 ∧ 0 ≤ (tableEnvelope C).w2 12659 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12659 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12659 162 ∧ 0 ≤ d.f1 12659 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12659 162 ∧ 0 ≤ d.w1 12659 162 ∧ 0 ≤ d.w2 12659 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12659 ≤ 2 * (228 / 100 : ℝ) / 12659 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12659 ≤ 2 * (370 / 100 : ℝ) / 12659 := by
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
    (completeRAData (tableEnvelope C) 12659 162).locationBound 12659 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12659 162).energyBound 12659 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12659 162) (d.f1 12659 162) d.f2 ≤
      32 * (((4619901731 / 1000000000000000000) : ℝ) + (24082459 / 15625000000000000) + (185223283 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12659 162) (d.w1 12659 162)
      (d.w2 12659 162) ≤
      32 * (((7404281 / 400000000000000000) : ℝ) + (1317001087 / 100000000000000000000) + (240599563 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12659 162) (d.f1 12659 162) d.f2 ≤
      ((4619901731 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4619901731 / 1000000000000000000)) * ((24082459 / 15625000000000000)) * (126 / 100) +
      2 * (((24082459 / 15625000000000000)) ^ 2 + 2 * ((4619901731 / 1000000000000000000)) * ((185223283 / 500000000000000000))) +
      6 * ((24082459 / 15625000000000000)) * ((185223283 / 500000000000000000)) * (126 / 100) + 8 * ((185223283 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12659 162) (d.f1 12659 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12659 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12659 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12659 162) (d.f1 12659 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12659 162) (d.w1 12659 162) (d.w2 12659 162)
  have hwexpr0 : 0 ≤ d.w0 12659 162 + d.w1 12659 162 * √(π / 2) +
      2 * d.w2 12659 162 + energyR16 12659 *
      radiusPolynomialRoot16 (d.w0 12659 162) (d.w1 12659 162) (d.w2 12659 162) := by
    positivity
  constructor
  · change (12659 : ℝ) ^ 8 * (mA 12659 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12659 162) (d.f1 12659 162) d.f2 + locationR16 12659 *
        radiusPolynomialRoot16 (d.f0 12659 162) (d.f1 12659 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12659 : ℝ) ^ 8 * (mA 12659 : ℝ) ^ 8 *
        ((((4619901731 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4619901731 / 1000000000000000000)) * ((24082459 / 15625000000000000)) * (126 / 100) +
          2 * (((24082459 / 15625000000000000)) ^ 2 + 2 * ((4619901731 / 1000000000000000000)) * ((185223283 / 500000000000000000))) +
          6 * ((24082459 / 15625000000000000)) * ((185223283 / 500000000000000000)) * (126 / 100) + 8 * ((185223283 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12659) *
          (32 * (((4619901731 / 1000000000000000000) : ℝ) + (24082459 / 15625000000000000) + (185223283 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12659 : ℝ) ^ 16 *
      (d.w0 12659 162 + d.w1 12659 162 * √(π / 2) + 2 * d.w2 12659 162 +
        energyR16 12659 * radiusPolynomialRoot16 (d.w0 12659 162) (d.w1 12659 162)
          (d.w2 12659 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12659 : ℝ) ^ 16 *
        (((7404281 / 400000000000000000) : ℝ) + ((1317001087 / 100000000000000000000)) * (126 / 100) + 2 * ((240599563 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12659) *
          (32 * (((7404281 / 400000000000000000) : ℝ) + (1317001087 / 100000000000000000000) + (240599563 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12659

/-! A coarse bound on the actual paper statistics constant at dimension 12660. -/
namespace BstLean.Part266.Row12660
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12658 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12658 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12658 128 ≤ (12912 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12912 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12660) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12660 : ℕ))
    (by norm_num : (12660 : ℕ) ≤ 16384)
  have ht : paperTail256 12660 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12660 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12660 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12660 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12660 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12660 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12658 128 * √(2 / (12660 : ℝ)) *
      (√(12660 : ℝ) + paperT0 12660 + paperTail256 12660) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12660 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12660 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12660 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12658 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12658 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12660 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12660

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12660
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12660 (61 / 100) 162 (17 / (100 * 12660)) (26 / (10 * 12660)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12660 (61 / 100) 162 (17 / (100 * 12660)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (96216003 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (380000017 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5247087713 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12660 / 12660 * (61 / 100)) ^ 4 * inverseRadius8 (12660 - 1) /
            envelopeGap 12660 (61 / 100) 162 (17 / (100 * 12660)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12660

namespace BstLean.Part266.Row12660
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12660 162 ≤ (4618990393 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12660 162 ≤ (770486619 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (1157417 / 3125000000000000)
  w0 : (tableEnvelope C).w0 12660 162 ≤ (1850631817 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12660 162 ≤ (263337821 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12660 162 ≤ (240542549 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (96216003 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (96216003 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (380000017 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5247087713 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3664439 / 1000000000) : ℝ) ≤ √(17 / (100 * 12660) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12660) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2193353631 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9746794563 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12660) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12660) ≤ (111707233 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12660) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12660 * (162 : ℝ) ^ 2 + 26 / (10 * 12660) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12660) : ℝ)) (tA 12660 * 162 ^ 2 + 26 / (10 * 12660)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3664439 / 1000000000))) * ((96216003 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3664439 / 1000000000)) ^ 3) * ((380000017 / 250000000000000000000000))) + ((5247087713 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3664439 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12660) : ℝ)) d.D d.V d.P (√(tA 12660) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3664439 / 1000000000)) ^ 2 * (((2193353631 / 1000000000000000)) * ((9746794563 / 250000000000000000)))) + ((5247087713 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12660) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3664439 / 1000000000)) * ((96216003 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12660) : ℝ)) (tA 12660 * 162 ^ 2 + 26 / (10 * 12660)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((96216003 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3664439 / 1000000000)) ^ 2) * ((380000017 / 250000000000000000000000)) + ((5247087713 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12660) : ℝ)) (√(26 / (10 * 12660) : ℝ)) d.D d.V d.P (√(tA 12660) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3664439 / 1000000000)) * (((2193353631 / 1000000000000000)) * ((9746794563 / 250000000000000000))) + ((5247087713 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12660) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((96216003 / 20000000000000000000) : ℝ) + ((5247087713 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12660

namespace BstLean.Part266.Row12660
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12660 162 ∧
    0 ≤ (tableEnvelope C).f1 12660 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12660 162 ∧
    0 ≤ (tableEnvelope C).w1 12660 162 ∧ 0 ≤ (tableEnvelope C).w2 12660 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12660 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12660 162 ∧ 0 ≤ d.f1 12660 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12660 162 ∧ 0 ≤ d.w1 12660 162 ∧ 0 ≤ d.w2 12660 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12660 ≤ 2 * (228 / 100 : ℝ) / 12660 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12660 ≤ 2 * (370 / 100 : ℝ) / 12660 := by
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
    (completeRAData (tableEnvelope C) 12660 162).locationBound 12660 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12660 162).energyBound 12660 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12660 162) (d.f1 12660 162) d.f2 ≤
      32 * (((4618990393 / 1000000000000000000) : ℝ) + (770486619 / 500000000000000000) + (1157417 / 3125000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12660 162) (d.w1 12660 162)
      (d.w2 12660 162) ≤
      32 * (((1850631817 / 100000000000000000000) : ℝ) + (263337821 / 20000000000000000000) + (240542549 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12660 162) (d.f1 12660 162) d.f2 ≤
      ((4618990393 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4618990393 / 1000000000000000000)) * ((770486619 / 500000000000000000)) * (126 / 100) +
      2 * (((770486619 / 500000000000000000)) ^ 2 + 2 * ((4618990393 / 1000000000000000000)) * ((1157417 / 3125000000000000))) +
      6 * ((770486619 / 500000000000000000)) * ((1157417 / 3125000000000000)) * (126 / 100) + 8 * ((1157417 / 3125000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12660 162) (d.f1 12660 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12660 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12660 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12660 162) (d.f1 12660 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12660 162) (d.w1 12660 162) (d.w2 12660 162)
  have hwexpr0 : 0 ≤ d.w0 12660 162 + d.w1 12660 162 * √(π / 2) +
      2 * d.w2 12660 162 + energyR16 12660 *
      radiusPolynomialRoot16 (d.w0 12660 162) (d.w1 12660 162) (d.w2 12660 162) := by
    positivity
  constructor
  · change (12660 : ℝ) ^ 8 * (mA 12660 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12660 162) (d.f1 12660 162) d.f2 + locationR16 12660 *
        radiusPolynomialRoot16 (d.f0 12660 162) (d.f1 12660 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12660 : ℝ) ^ 8 * (mA 12660 : ℝ) ^ 8 *
        ((((4618990393 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4618990393 / 1000000000000000000)) * ((770486619 / 500000000000000000)) * (126 / 100) +
          2 * (((770486619 / 500000000000000000)) ^ 2 + 2 * ((4618990393 / 1000000000000000000)) * ((1157417 / 3125000000000000))) +
          6 * ((770486619 / 500000000000000000)) * ((1157417 / 3125000000000000)) * (126 / 100) + 8 * ((1157417 / 3125000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12660) *
          (32 * (((4618990393 / 1000000000000000000) : ℝ) + (770486619 / 500000000000000000) + (1157417 / 3125000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12660 : ℝ) ^ 16 *
      (d.w0 12660 162 + d.w1 12660 162 * √(π / 2) + 2 * d.w2 12660 162 +
        energyR16 12660 * radiusPolynomialRoot16 (d.w0 12660 162) (d.w1 12660 162)
          (d.w2 12660 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12660 : ℝ) ^ 16 *
        (((1850631817 / 100000000000000000000) : ℝ) + ((263337821 / 20000000000000000000)) * (126 / 100) + 2 * ((240542549 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12660) *
          (32 * (((1850631817 / 100000000000000000000) : ℝ) + (263337821 / 20000000000000000000) + (240542549 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12660

/-! A coarse bound on the actual paper statistics constant at dimension 12661. -/
namespace BstLean.Part266.Row12661
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12659 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12659 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12659 128 ≤ (12913 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12913 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12661) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12661 : ℕ))
    (by norm_num : (12661 : ℕ) ≤ 16384)
  have ht : paperTail256 12661 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12661 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12661 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12661 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12661 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12661 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12659 128 * √(2 / (12661 : ℝ)) *
      (√(12661 : ℝ) + paperT0 12661 + paperTail256 12661) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12661 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12661 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12661 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12659 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12659 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12661 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12661

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12661
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12661 (61 / 100) 162 (17 / (100 * 12661)) (26 / (10 * 12661)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12661 (61 / 100) 162 (17 / (100 * 12661)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (480966027 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1519519891 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5243741109 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12661 / 12661 * (61 / 100)) ^ 4 * inverseRadius8 (12661 - 1) /
            envelopeGap 12661 (61 / 100) 162 (17 / (100 * 12661)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12661

namespace BstLean.Part266.Row12661
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12661 162 ≤ (4618075731 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12661 162 ≤ (1540668359 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (185150117 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12661 162 ≤ (1850192789 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12661 162 ≤ (329094217 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12661 162 ≤ (480971107 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (480966027 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (480966027 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1519519891 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5243741109 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((732859 / 200000000) : ℝ) ≤ √(17 / (100 * 12661) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12661) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2193093767 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (311848157 / 8000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12661) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12661) ≤ (11169841 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12661) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12661 * (162 : ℝ) ^ 2 + 26 / (10 * 12661) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12661) : ℝ)) (tA 12661 * 162 ^ 2 + 26 / (10 * 12661)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((732859 / 200000000))) * ((480966027 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((732859 / 200000000)) ^ 3) * ((1519519891 / 1000000000000000000000000))) + ((5243741109 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((732859 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12661) : ℝ)) d.D d.V d.P (√(tA 12661) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((732859 / 200000000)) ^ 2 * (((2193093767 / 1000000000000000)) * ((311848157 / 8000000000000000)))) + ((5243741109 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12661) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((732859 / 200000000)) * ((480966027 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12661) : ℝ)) (tA 12661 * 162 ^ 2 + 26 / (10 * 12661)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((480966027 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((732859 / 200000000)) ^ 2) * ((1519519891 / 1000000000000000000000000)) + ((5243741109 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12661) : ℝ)) (√(26 / (10 * 12661) : ℝ)) d.D d.V d.P (√(tA 12661) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((732859 / 200000000)) * (((2193093767 / 1000000000000000)) * ((311848157 / 8000000000000000))) + ((5243741109 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12661) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((480966027 / 100000000000000000000) : ℝ) + ((5243741109 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12661

namespace BstLean.Part266.Row12661
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12661 162 ∧
    0 ≤ (tableEnvelope C).f1 12661 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12661 162 ∧
    0 ≤ (tableEnvelope C).w1 12661 162 ∧ 0 ≤ (tableEnvelope C).w2 12661 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12661 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12661 162 ∧ 0 ≤ d.f1 12661 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12661 162 ∧ 0 ≤ d.w1 12661 162 ∧ 0 ≤ d.w2 12661 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12661 ≤ 2 * (228 / 100 : ℝ) / 12661 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12661 ≤ 2 * (370 / 100 : ℝ) / 12661 := by
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
    (completeRAData (tableEnvelope C) 12661 162).locationBound 12661 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12661 162).energyBound 12661 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12661 162) (d.f1 12661 162) d.f2 ≤
      32 * (((4618075731 / 1000000000000000000) : ℝ) + (1540668359 / 1000000000000000000) + (185150117 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12661 162) (d.w1 12661 162)
      (d.w2 12661 162) ≤
      32 * (((1850192789 / 100000000000000000000) : ℝ) + (329094217 / 25000000000000000000) + (480971107 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12661 162) (d.f1 12661 162) d.f2 ≤
      ((4618075731 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4618075731 / 1000000000000000000)) * ((1540668359 / 1000000000000000000)) * (126 / 100) +
      2 * (((1540668359 / 1000000000000000000)) ^ 2 + 2 * ((4618075731 / 1000000000000000000)) * ((185150117 / 500000000000000000))) +
      6 * ((1540668359 / 1000000000000000000)) * ((185150117 / 500000000000000000)) * (126 / 100) + 8 * ((185150117 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12661 162) (d.f1 12661 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12661 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12661 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12661 162) (d.f1 12661 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12661 162) (d.w1 12661 162) (d.w2 12661 162)
  have hwexpr0 : 0 ≤ d.w0 12661 162 + d.w1 12661 162 * √(π / 2) +
      2 * d.w2 12661 162 + energyR16 12661 *
      radiusPolynomialRoot16 (d.w0 12661 162) (d.w1 12661 162) (d.w2 12661 162) := by
    positivity
  constructor
  · change (12661 : ℝ) ^ 8 * (mA 12661 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12661 162) (d.f1 12661 162) d.f2 + locationR16 12661 *
        radiusPolynomialRoot16 (d.f0 12661 162) (d.f1 12661 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12661 : ℝ) ^ 8 * (mA 12661 : ℝ) ^ 8 *
        ((((4618075731 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4618075731 / 1000000000000000000)) * ((1540668359 / 1000000000000000000)) * (126 / 100) +
          2 * (((1540668359 / 1000000000000000000)) ^ 2 + 2 * ((4618075731 / 1000000000000000000)) * ((185150117 / 500000000000000000))) +
          6 * ((1540668359 / 1000000000000000000)) * ((185150117 / 500000000000000000)) * (126 / 100) + 8 * ((185150117 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12661) *
          (32 * (((4618075731 / 1000000000000000000) : ℝ) + (1540668359 / 1000000000000000000) + (185150117 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12661 : ℝ) ^ 16 *
      (d.w0 12661 162 + d.w1 12661 162 * √(π / 2) + 2 * d.w2 12661 162 +
        energyR16 12661 * radiusPolynomialRoot16 (d.w0 12661 162) (d.w1 12661 162)
          (d.w2 12661 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12661 : ℝ) ^ 16 *
        (((1850192789 / 100000000000000000000) : ℝ) + ((329094217 / 25000000000000000000)) * (126 / 100) + 2 * ((480971107 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12661) *
          (32 * (((1850192789 / 100000000000000000000) : ℝ) + (329094217 / 25000000000000000000) + (480971107 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12661

/-! A coarse bound on the actual paper statistics constant at dimension 12662. -/
namespace BstLean.Part266.Row12662
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12660 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12660 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12660 128 ≤ (12914 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12914 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12662) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12662 : ℕ))
    (by norm_num : (12662 : ℕ) ≤ 16384)
  have ht : paperTail256 12662 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12662 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12662 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12662 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12662 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12662 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12660 128 * √(2 / (12662 : ℝ)) *
      (√(12662 : ℝ) + paperT0 12662 + paperTail256 12662) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12662 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12662 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12662 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12660 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12660 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12662 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12662

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12662
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12662 (61 / 100) 162 (17 / (100 * 12662)) (26 / (10 * 12662)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12662 (61 / 100) 162 (17 / (100 * 12662)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (19234083 / 4000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (47469997 / 31250000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5240396909 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12662 / 12662 * (61 / 100)) ^ 4 * inverseRadius8 (12662 - 1) /
            envelopeGap 12662 (61 / 100) 162 (17 / (100 * 12662)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12662

namespace BstLean.Part266.Row12662
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12662 162 ≤ (144286407 / 31250000000000000)
  f1 : (tableEnvelope C).f1 12662 162 ≤ (77018221 / 50000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (23139197 / 62500000000000000)
  w0 : (tableEnvelope C).w0 12662 162 ≤ (92487733 / 5000000000000000000)
  w1 : (tableEnvelope C).w1 12662 162 ≤ (164508137 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 12662 162 ≤ (7513393 / 1562500000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (19234083 / 4000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (19234083 / 4000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (47469997 / 31250000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5240396909 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((73283 / 20000000) : ℝ) ≤ √(17 / (100 * 12662) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12662) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (438566791 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38974862463 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12662) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12662) ≤ (27922397 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12662) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12662 * (162 : ℝ) ^ 2 + 26 / (10 * 12662) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12662) : ℝ)) (tA 12662 * 162 ^ 2 + 26 / (10 * 12662)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((73283 / 20000000))) * ((19234083 / 4000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((73283 / 20000000)) ^ 3) * ((47469997 / 31250000000000000000000))) + ((5240396909 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((73283 / 20000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12662) : ℝ)) d.D d.V d.P (√(tA 12662) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((73283 / 20000000)) ^ 2 * (((438566791 / 200000000000000)) * ((38974862463 / 1000000000000000000)))) + ((5240396909 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12662) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((73283 / 20000000)) * ((19234083 / 4000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12662) : ℝ)) (tA 12662 * 162 ^ 2 + 26 / (10 * 12662)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((19234083 / 4000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((73283 / 20000000)) ^ 2) * ((47469997 / 31250000000000000000000)) + ((5240396909 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12662) : ℝ)) (√(26 / (10 * 12662) : ℝ)) d.D d.V d.P (√(tA 12662) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((73283 / 20000000)) * (((438566791 / 200000000000000)) * ((38974862463 / 1000000000000000000))) + ((5240396909 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12662) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((19234083 / 4000000000000000000) : ℝ) + ((5240396909 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12662

namespace BstLean.Part266.Row12662
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12662 162 ∧
    0 ≤ (tableEnvelope C).f1 12662 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12662 162 ∧
    0 ≤ (tableEnvelope C).w1 12662 162 ∧ 0 ≤ (tableEnvelope C).w2 12662 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12662 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12662 162 ∧ 0 ≤ d.f1 12662 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12662 162 ∧ 0 ≤ d.w1 12662 162 ∧ 0 ≤ d.w2 12662 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12662 ≤ 2 * (228 / 100 : ℝ) / 12662 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12662 ≤ 2 * (370 / 100 : ℝ) / 12662 := by
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
    (completeRAData (tableEnvelope C) 12662 162).locationBound 12662 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12662 162).energyBound 12662 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12662 162) (d.f1 12662 162) d.f2 ≤
      32 * (((144286407 / 31250000000000000) : ℝ) + (77018221 / 50000000000000000) + (23139197 / 62500000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12662 162) (d.w1 12662 162)
      (d.w2 12662 162) ≤
      32 * (((92487733 / 5000000000000000000) : ℝ) + (164508137 / 12500000000000000000) + (7513393 / 1562500000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12662 162) (d.f1 12662 162) d.f2 ≤
      ((144286407 / 31250000000000000) : ℝ) ^ 2 + 2 * ((144286407 / 31250000000000000)) * ((77018221 / 50000000000000000)) * (126 / 100) +
      2 * (((77018221 / 50000000000000000)) ^ 2 + 2 * ((144286407 / 31250000000000000)) * ((23139197 / 62500000000000000))) +
      6 * ((77018221 / 50000000000000000)) * ((23139197 / 62500000000000000)) * (126 / 100) + 8 * ((23139197 / 62500000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12662 162) (d.f1 12662 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12662 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12662 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12662 162) (d.f1 12662 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12662 162) (d.w1 12662 162) (d.w2 12662 162)
  have hwexpr0 : 0 ≤ d.w0 12662 162 + d.w1 12662 162 * √(π / 2) +
      2 * d.w2 12662 162 + energyR16 12662 *
      radiusPolynomialRoot16 (d.w0 12662 162) (d.w1 12662 162) (d.w2 12662 162) := by
    positivity
  constructor
  · change (12662 : ℝ) ^ 8 * (mA 12662 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12662 162) (d.f1 12662 162) d.f2 + locationR16 12662 *
        radiusPolynomialRoot16 (d.f0 12662 162) (d.f1 12662 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12662 : ℝ) ^ 8 * (mA 12662 : ℝ) ^ 8 *
        ((((144286407 / 31250000000000000) : ℝ) ^ 2 + 2 * ((144286407 / 31250000000000000)) * ((77018221 / 50000000000000000)) * (126 / 100) +
          2 * (((77018221 / 50000000000000000)) ^ 2 + 2 * ((144286407 / 31250000000000000)) * ((23139197 / 62500000000000000))) +
          6 * ((77018221 / 50000000000000000)) * ((23139197 / 62500000000000000)) * (126 / 100) + 8 * ((23139197 / 62500000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12662) *
          (32 * (((144286407 / 31250000000000000) : ℝ) + (77018221 / 50000000000000000) + (23139197 / 62500000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12662 : ℝ) ^ 16 *
      (d.w0 12662 162 + d.w1 12662 162 * √(π / 2) + 2 * d.w2 12662 162 +
        energyR16 12662 * radiusPolynomialRoot16 (d.w0 12662 162) (d.w1 12662 162)
          (d.w2 12662 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12662 : ℝ) ^ 16 *
        (((92487733 / 5000000000000000000) : ℝ) + ((164508137 / 12500000000000000000)) * (126 / 100) + 2 * ((7513393 / 1562500000000000000)) +
          (2 * (370 / 100 : ℝ) / 12662) *
          (32 * (((92487733 / 5000000000000000000) : ℝ) + (164508137 / 12500000000000000000) + (7513393 / 1562500000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12662

/-! A coarse bound on the actual paper statistics constant at dimension 12663. -/
namespace BstLean.Part266.Row12663
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12661 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12661 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12661 128 ≤ (12915 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12915 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12663) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12663 : ℕ))
    (by norm_num : (12663 : ℕ) ≤ 16384)
  have ht : paperTail256 12663 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12663 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12663 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12663 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12663 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12663 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12661 128 * √(2 / (12663 : ℝ)) *
      (√(12663 : ℝ) + paperT0 12663 + paperTail256 12663) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12663 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12663 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12663 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12661 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12661 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12663 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12663

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12663
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12663 (61 / 100) 162 (17 / (100 * 12663)) (26 / (10 * 12663)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12663 (61 / 100) 162 (17 / (100 * 12663)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (480738159 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (759280053 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5237055111 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12663 / 12663 * (61 / 100)) ^ 4 * inverseRadius8 (12663 - 1) /
            envelopeGap 12663 (61 / 100) 162 (17 / (100 * 12663)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12663

namespace BstLean.Part266.Row12663
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12663 162 ≤ (4616254629 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12663 162 ≤ (1540060577 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (370154091 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12663 162 ≤ (924658341 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12663 162 ≤ (328938357 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12663 162 ≤ (480743233 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (480738159 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (480738159 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (759280053 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5237055111 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((732801 / 200000000) : ℝ) ≤ √(17 / (100 * 12663) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12663) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2192574193 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38968706753 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12663) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12663) ≤ (436253 / 3906250000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12663) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12663 * (162 : ℝ) ^ 2 + 26 / (10 * 12663) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12663) : ℝ)) (tA 12663 * 162 ^ 2 + 26 / (10 * 12663)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((732801 / 200000000))) * ((480738159 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((732801 / 200000000)) ^ 3) * ((759280053 / 500000000000000000000000))) + ((5237055111 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((732801 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12663) : ℝ)) d.D d.V d.P (√(tA 12663) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((732801 / 200000000)) ^ 2 * (((2192574193 / 1000000000000000)) * ((38968706753 / 1000000000000000000)))) + ((5237055111 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12663) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((732801 / 200000000)) * ((480738159 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12663) : ℝ)) (tA 12663 * 162 ^ 2 + 26 / (10 * 12663)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((480738159 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((732801 / 200000000)) ^ 2) * ((759280053 / 500000000000000000000000)) + ((5237055111 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12663) : ℝ)) (√(26 / (10 * 12663) : ℝ)) d.D d.V d.P (√(tA 12663) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((732801 / 200000000)) * (((2192574193 / 1000000000000000)) * ((38968706753 / 1000000000000000000))) + ((5237055111 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12663) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((480738159 / 100000000000000000000) : ℝ) + ((5237055111 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12663

namespace BstLean.Part266.Row12663
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12663 162 ∧
    0 ≤ (tableEnvelope C).f1 12663 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12663 162 ∧
    0 ≤ (tableEnvelope C).w1 12663 162 ∧ 0 ≤ (tableEnvelope C).w2 12663 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12663 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12663 162 ∧ 0 ≤ d.f1 12663 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12663 162 ∧ 0 ≤ d.w1 12663 162 ∧ 0 ≤ d.w2 12663 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12663 ≤ 2 * (228 / 100 : ℝ) / 12663 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12663 ≤ 2 * (370 / 100 : ℝ) / 12663 := by
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
    (completeRAData (tableEnvelope C) 12663 162).locationBound 12663 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12663 162).energyBound 12663 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12663 162) (d.f1 12663 162) d.f2 ≤
      32 * (((4616254629 / 1000000000000000000) : ℝ) + (1540060577 / 1000000000000000000) + (370154091 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12663 162) (d.w1 12663 162)
      (d.w2 12663 162) ≤
      32 * (((924658341 / 50000000000000000000) : ℝ) + (328938357 / 25000000000000000000) + (480743233 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12663 162) (d.f1 12663 162) d.f2 ≤
      ((4616254629 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4616254629 / 1000000000000000000)) * ((1540060577 / 1000000000000000000)) * (126 / 100) +
      2 * (((1540060577 / 1000000000000000000)) ^ 2 + 2 * ((4616254629 / 1000000000000000000)) * ((370154091 / 1000000000000000000))) +
      6 * ((1540060577 / 1000000000000000000)) * ((370154091 / 1000000000000000000)) * (126 / 100) + 8 * ((370154091 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12663 162) (d.f1 12663 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12663 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12663 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12663 162) (d.f1 12663 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12663 162) (d.w1 12663 162) (d.w2 12663 162)
  have hwexpr0 : 0 ≤ d.w0 12663 162 + d.w1 12663 162 * √(π / 2) +
      2 * d.w2 12663 162 + energyR16 12663 *
      radiusPolynomialRoot16 (d.w0 12663 162) (d.w1 12663 162) (d.w2 12663 162) := by
    positivity
  constructor
  · change (12663 : ℝ) ^ 8 * (mA 12663 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12663 162) (d.f1 12663 162) d.f2 + locationR16 12663 *
        radiusPolynomialRoot16 (d.f0 12663 162) (d.f1 12663 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12663 : ℝ) ^ 8 * (mA 12663 : ℝ) ^ 8 *
        ((((4616254629 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4616254629 / 1000000000000000000)) * ((1540060577 / 1000000000000000000)) * (126 / 100) +
          2 * (((1540060577 / 1000000000000000000)) ^ 2 + 2 * ((4616254629 / 1000000000000000000)) * ((370154091 / 1000000000000000000))) +
          6 * ((1540060577 / 1000000000000000000)) * ((370154091 / 1000000000000000000)) * (126 / 100) + 8 * ((370154091 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12663) *
          (32 * (((4616254629 / 1000000000000000000) : ℝ) + (1540060577 / 1000000000000000000) + (370154091 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12663 : ℝ) ^ 16 *
      (d.w0 12663 162 + d.w1 12663 162 * √(π / 2) + 2 * d.w2 12663 162 +
        energyR16 12663 * radiusPolynomialRoot16 (d.w0 12663 162) (d.w1 12663 162)
          (d.w2 12663 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12663 : ℝ) ^ 16 *
        (((924658341 / 50000000000000000000) : ℝ) + ((328938357 / 25000000000000000000)) * (126 / 100) + 2 * ((480743233 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12663) *
          (32 * (((924658341 / 50000000000000000000) : ℝ) + (328938357 / 25000000000000000000) + (480743233 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12663

/-! A coarse bound on the actual paper statistics constant at dimension 12664. -/
namespace BstLean.Part266.Row12664
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12662 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12662 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12662 128 ≤ (12916 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12916 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12664) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12664 : ℕ))
    (by norm_num : (12664 : ℕ) ≤ 16384)
  have ht : paperTail256 12664 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12664 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12664 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12664 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12664 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12664 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12662 128 * √(2 / (12664 : ℝ)) *
      (√(12664 : ℝ) + paperT0 12664 + paperTail256 12664) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12664 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12664 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12664 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12662 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12662 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12664 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12664

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12664
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12664 (61 / 100) 162 (17 / (100 * 12664)) (26 / (10 * 12664)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12664 (61 / 100) 162 (17 / (100 * 12664)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (480624279 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1518080497 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (10222101 / 1953125000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12664 / 12664 * (61 / 100)) ^ 4 * inverseRadius8 (12664 - 1) /
            envelopeGap 12664 (61 / 100) 162 (17 / (100 * 12664)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12664

namespace BstLean.Part266.Row12664
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12664 162 ≤ (461534091 / 100000000000000000)
  f1 : (tableEnvelope C).f1 12664 162 ≤ (1539755993 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (46260119 / 125000000000000000)
  w0 : (tableEnvelope C).w0 12664 162 ≤ (1848878107 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12664 162 ≤ (263088301 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12664 162 ≤ (480629349 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (480624279 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (480624279 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1518080497 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (10222101 / 1953125000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3663861 / 1000000000) : ℝ) ≤ √(17 / (100 * 12664) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12664) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2192314483 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (2435159531 / 62500000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12664) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12664) ≤ (2233439 / 20000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12664) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12664 * (162 : ℝ) ^ 2 + 26 / (10 * 12664) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12664) : ℝ)) (tA 12664 * 162 ^ 2 + 26 / (10 * 12664)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3663861 / 1000000000))) * ((480624279 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3663861 / 1000000000)) ^ 3) * ((1518080497 / 1000000000000000000000000))) + ((10222101 / 1953125000000000000000)) * (3 / 2 * (39895 / 100000) / ((3663861 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12664) : ℝ)) d.D d.V d.P (√(tA 12664) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3663861 / 1000000000)) ^ 2 * (((2192314483 / 1000000000000000)) * ((2435159531 / 62500000000000000)))) + ((10222101 / 1953125000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12664) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3663861 / 1000000000)) * ((480624279 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12664) : ℝ)) (tA 12664 * 162 ^ 2 + 26 / (10 * 12664)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((480624279 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3663861 / 1000000000)) ^ 2) * ((1518080497 / 1000000000000000000000000)) + ((10222101 / 1953125000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12664) : ℝ)) (√(26 / (10 * 12664) : ℝ)) d.D d.V d.P (√(tA 12664) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3663861 / 1000000000)) * (((2192314483 / 1000000000000000)) * ((2435159531 / 62500000000000000))) + ((10222101 / 1953125000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12664) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((480624279 / 100000000000000000000) : ℝ) + ((10222101 / 1953125000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12664

namespace BstLean.Part266.Row12664
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12664 162 ∧
    0 ≤ (tableEnvelope C).f1 12664 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12664 162 ∧
    0 ≤ (tableEnvelope C).w1 12664 162 ∧ 0 ≤ (tableEnvelope C).w2 12664 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12664 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12664 162 ∧ 0 ≤ d.f1 12664 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12664 162 ∧ 0 ≤ d.w1 12664 162 ∧ 0 ≤ d.w2 12664 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12664 ≤ 2 * (228 / 100 : ℝ) / 12664 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12664 ≤ 2 * (370 / 100 : ℝ) / 12664 := by
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
    (completeRAData (tableEnvelope C) 12664 162).locationBound 12664 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12664 162).energyBound 12664 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12664 162) (d.f1 12664 162) d.f2 ≤
      32 * (((461534091 / 100000000000000000) : ℝ) + (1539755993 / 1000000000000000000) + (46260119 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12664 162) (d.w1 12664 162)
      (d.w2 12664 162) ≤
      32 * (((1848878107 / 100000000000000000000) : ℝ) + (263088301 / 20000000000000000000) + (480629349 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12664 162) (d.f1 12664 162) d.f2 ≤
      ((461534091 / 100000000000000000) : ℝ) ^ 2 + 2 * ((461534091 / 100000000000000000)) * ((1539755993 / 1000000000000000000)) * (126 / 100) +
      2 * (((1539755993 / 1000000000000000000)) ^ 2 + 2 * ((461534091 / 100000000000000000)) * ((46260119 / 125000000000000000))) +
      6 * ((1539755993 / 1000000000000000000)) * ((46260119 / 125000000000000000)) * (126 / 100) + 8 * ((46260119 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12664 162) (d.f1 12664 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12664 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12664 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12664 162) (d.f1 12664 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12664 162) (d.w1 12664 162) (d.w2 12664 162)
  have hwexpr0 : 0 ≤ d.w0 12664 162 + d.w1 12664 162 * √(π / 2) +
      2 * d.w2 12664 162 + energyR16 12664 *
      radiusPolynomialRoot16 (d.w0 12664 162) (d.w1 12664 162) (d.w2 12664 162) := by
    positivity
  constructor
  · change (12664 : ℝ) ^ 8 * (mA 12664 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12664 162) (d.f1 12664 162) d.f2 + locationR16 12664 *
        radiusPolynomialRoot16 (d.f0 12664 162) (d.f1 12664 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12664 : ℝ) ^ 8 * (mA 12664 : ℝ) ^ 8 *
        ((((461534091 / 100000000000000000) : ℝ) ^ 2 + 2 * ((461534091 / 100000000000000000)) * ((1539755993 / 1000000000000000000)) * (126 / 100) +
          2 * (((1539755993 / 1000000000000000000)) ^ 2 + 2 * ((461534091 / 100000000000000000)) * ((46260119 / 125000000000000000))) +
          6 * ((1539755993 / 1000000000000000000)) * ((46260119 / 125000000000000000)) * (126 / 100) + 8 * ((46260119 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12664) *
          (32 * (((461534091 / 100000000000000000) : ℝ) + (1539755993 / 1000000000000000000) + (46260119 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12664 : ℝ) ^ 16 *
      (d.w0 12664 162 + d.w1 12664 162 * √(π / 2) + 2 * d.w2 12664 162 +
        energyR16 12664 * radiusPolynomialRoot16 (d.w0 12664 162) (d.w1 12664 162)
          (d.w2 12664 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12664 : ℝ) ^ 16 *
        (((1848878107 / 100000000000000000000) : ℝ) + ((263088301 / 20000000000000000000)) * (126 / 100) + 2 * ((480629349 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12664) *
          (32 * (((1848878107 / 100000000000000000000) : ℝ) + (263088301 / 20000000000000000000) + (480629349 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12664

/-! A coarse bound on the actual paper statistics constant at dimension 12665. -/
namespace BstLean.Part266.Row12665
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12663 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12663 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12663 128 ≤ (12917 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12917 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12665) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12665 : ℕ))
    (by norm_num : (12665 : ℕ) ≤ 16384)
  have ht : paperTail256 12665 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12665 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12665 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12665 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12665 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12665 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12663 128 * √(2 / (12665 : ℝ)) *
      (√(12665 : ℝ) + paperT0 12665 + paperTail256 12665) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12665 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12665 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12665 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12663 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12663 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12665 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12665

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12665
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12665 (61 / 100) 162 (17 / (100 * 12665)) (26 / (10 * 12665)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12665 (61 / 100) 162 (17 / (100 * 12665)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (240255217 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (758800539 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5230378711 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12665 / 12665 * (61 / 100)) ^ 4 * inverseRadius8 (12665 - 1) /
            envelopeGap 12665 (61 / 100) 162 (17 / (100 * 12665)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12665

namespace BstLean.Part266.Row12665
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12665 162 ≤ (4614431143 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12665 162 ≤ (1539452347 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (185003967 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12665 162 ≤ (184844043 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 12665 162 ≤ (263026009 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12665 162 ≤ (480515501 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (240255217 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (240255217 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (758800539 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5230378711 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((915929 / 250000000) : ℝ) ≤ √(17 / (100 * 12665) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12665) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1096027411 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19478199853 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12665) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12665) ≤ (27915783 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12665) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12665 * (162 : ℝ) ^ 2 + 26 / (10 * 12665) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12665) : ℝ)) (tA 12665 * 162 ^ 2 + 26 / (10 * 12665)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((915929 / 250000000))) * ((240255217 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((915929 / 250000000)) ^ 3) * ((758800539 / 500000000000000000000000))) + ((5230378711 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((915929 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12665) : ℝ)) d.D d.V d.P (√(tA 12665) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((915929 / 250000000)) ^ 2 * (((1096027411 / 500000000000000)) * ((19478199853 / 500000000000000000)))) + ((5230378711 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12665) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((915929 / 250000000)) * ((240255217 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12665) : ℝ)) (tA 12665 * 162 ^ 2 + 26 / (10 * 12665)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((240255217 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((915929 / 250000000)) ^ 2) * ((758800539 / 500000000000000000000000)) + ((5230378711 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12665) : ℝ)) (√(26 / (10 * 12665) : ℝ)) d.D d.V d.P (√(tA 12665) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((915929 / 250000000)) * (((1096027411 / 500000000000000)) * ((19478199853 / 500000000000000000))) + ((5230378711 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12665) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((240255217 / 50000000000000000000) : ℝ) + ((5230378711 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12665

namespace BstLean.Part266.Row12665
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12665 162 ∧
    0 ≤ (tableEnvelope C).f1 12665 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12665 162 ∧
    0 ≤ (tableEnvelope C).w1 12665 162 ∧ 0 ≤ (tableEnvelope C).w2 12665 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12665 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12665 162 ∧ 0 ≤ d.f1 12665 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12665 162 ∧ 0 ≤ d.w1 12665 162 ∧ 0 ≤ d.w2 12665 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12665 ≤ 2 * (228 / 100 : ℝ) / 12665 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12665 ≤ 2 * (370 / 100 : ℝ) / 12665 := by
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
    (completeRAData (tableEnvelope C) 12665 162).locationBound 12665 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12665 162).energyBound 12665 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12665 162) (d.f1 12665 162) d.f2 ≤
      32 * (((4614431143 / 1000000000000000000) : ℝ) + (1539452347 / 1000000000000000000) + (185003967 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12665 162) (d.w1 12665 162)
      (d.w2 12665 162) ≤
      32 * (((184844043 / 10000000000000000000) : ℝ) + (263026009 / 20000000000000000000) + (480515501 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12665 162) (d.f1 12665 162) d.f2 ≤
      ((4614431143 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4614431143 / 1000000000000000000)) * ((1539452347 / 1000000000000000000)) * (126 / 100) +
      2 * (((1539452347 / 1000000000000000000)) ^ 2 + 2 * ((4614431143 / 1000000000000000000)) * ((185003967 / 500000000000000000))) +
      6 * ((1539452347 / 1000000000000000000)) * ((185003967 / 500000000000000000)) * (126 / 100) + 8 * ((185003967 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12665 162) (d.f1 12665 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12665 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12665 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12665 162) (d.f1 12665 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12665 162) (d.w1 12665 162) (d.w2 12665 162)
  have hwexpr0 : 0 ≤ d.w0 12665 162 + d.w1 12665 162 * √(π / 2) +
      2 * d.w2 12665 162 + energyR16 12665 *
      radiusPolynomialRoot16 (d.w0 12665 162) (d.w1 12665 162) (d.w2 12665 162) := by
    positivity
  constructor
  · change (12665 : ℝ) ^ 8 * (mA 12665 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12665 162) (d.f1 12665 162) d.f2 + locationR16 12665 *
        radiusPolynomialRoot16 (d.f0 12665 162) (d.f1 12665 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12665 : ℝ) ^ 8 * (mA 12665 : ℝ) ^ 8 *
        ((((4614431143 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4614431143 / 1000000000000000000)) * ((1539452347 / 1000000000000000000)) * (126 / 100) +
          2 * (((1539452347 / 1000000000000000000)) ^ 2 + 2 * ((4614431143 / 1000000000000000000)) * ((185003967 / 500000000000000000))) +
          6 * ((1539452347 / 1000000000000000000)) * ((185003967 / 500000000000000000)) * (126 / 100) + 8 * ((185003967 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12665) *
          (32 * (((4614431143 / 1000000000000000000) : ℝ) + (1539452347 / 1000000000000000000) + (185003967 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12665 : ℝ) ^ 16 *
      (d.w0 12665 162 + d.w1 12665 162 * √(π / 2) + 2 * d.w2 12665 162 +
        energyR16 12665 * radiusPolynomialRoot16 (d.w0 12665 162) (d.w1 12665 162)
          (d.w2 12665 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12665 : ℝ) ^ 16 *
        (((184844043 / 10000000000000000000) : ℝ) + ((263026009 / 20000000000000000000)) * (126 / 100) + 2 * ((480515501 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12665) *
          (32 * (((184844043 / 10000000000000000000) : ℝ) + (263026009 / 20000000000000000000) + (480515501 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12665

/-! A coarse bound on the actual paper statistics constant at dimension 12666. -/
namespace BstLean.Part266.Row12666
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12664 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12664 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12664 128 ≤ (12918 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12918 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12666) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12666 : ℕ))
    (by norm_num : (12666 : ℕ) ≤ 16384)
  have ht : paperTail256 12666 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12666 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12666 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12666 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12666 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12666 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12664 128 * √(2 / (12666 : ℝ)) *
      (√(12666 : ℝ) + paperT0 12666 + paperTail256 12666) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12666 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12666 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12666 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12664 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12664 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12666 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12666

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12666
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12666 (61 / 100) 162 (17 / (100 * 12666)) (26 / (10 * 12666)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12666 (61 / 100) 162 (17 / (100 * 12666)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (240198313 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1517121849 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2613522053 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12666 / 12666 * (61 / 100)) ^ 4 * inverseRadius8 (12666 - 1) /
            envelopeGap 12666 (61 / 100) 162 (17 / (100 * 12666)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12666

namespace BstLean.Part266.Row12666
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12666 162 ≤ (4613521693 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12666 162 ≤ (1539148801 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (18496747 / 50000000000000000)
  w0 : (tableEnvelope C).w0 12666 162 ≤ (924001453 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12666 162 ≤ (1314818691 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12666 162 ≤ (48040169 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (240198313 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (240198313 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1517121849 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2613522053 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3663571 / 1000000000) : ℝ) ≤ √(17 / (100 * 12666) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12666) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1095897607 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19475124191 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12666) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12666) ≤ (27913579 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12666) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12666 * (162 : ℝ) ^ 2 + 26 / (10 * 12666) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12666) : ℝ)) (tA 12666 * 162 ^ 2 + 26 / (10 * 12666)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3663571 / 1000000000))) * ((240198313 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3663571 / 1000000000)) ^ 3) * ((1517121849 / 1000000000000000000000000))) + ((2613522053 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3663571 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12666) : ℝ)) d.D d.V d.P (√(tA 12666) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3663571 / 1000000000)) ^ 2 * (((1095897607 / 500000000000000)) * ((19475124191 / 500000000000000000)))) + ((2613522053 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12666) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3663571 / 1000000000)) * ((240198313 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12666) : ℝ)) (tA 12666 * 162 ^ 2 + 26 / (10 * 12666)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((240198313 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3663571 / 1000000000)) ^ 2) * ((1517121849 / 1000000000000000000000000)) + ((2613522053 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12666) : ℝ)) (√(26 / (10 * 12666) : ℝ)) d.D d.V d.P (√(tA 12666) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3663571 / 1000000000)) * (((1095897607 / 500000000000000)) * ((19475124191 / 500000000000000000))) + ((2613522053 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12666) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((240198313 / 50000000000000000000) : ℝ) + ((2613522053 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12666

namespace BstLean.Part266.Row12666
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12666 162 ∧
    0 ≤ (tableEnvelope C).f1 12666 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12666 162 ∧
    0 ≤ (tableEnvelope C).w1 12666 162 ∧ 0 ≤ (tableEnvelope C).w2 12666 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12666 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12666 162 ∧ 0 ≤ d.f1 12666 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12666 162 ∧ 0 ≤ d.w1 12666 162 ∧ 0 ≤ d.w2 12666 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12666 ≤ 2 * (228 / 100 : ℝ) / 12666 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12666 ≤ 2 * (370 / 100 : ℝ) / 12666 := by
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
    (completeRAData (tableEnvelope C) 12666 162).locationBound 12666 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12666 162).energyBound 12666 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12666 162) (d.f1 12666 162) d.f2 ≤
      32 * (((4613521693 / 1000000000000000000) : ℝ) + (1539148801 / 1000000000000000000) + (18496747 / 50000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12666 162) (d.w1 12666 162)
      (d.w2 12666 162) ≤
      32 * (((924001453 / 50000000000000000000) : ℝ) + (1314818691 / 100000000000000000000) + (48040169 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12666 162) (d.f1 12666 162) d.f2 ≤
      ((4613521693 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4613521693 / 1000000000000000000)) * ((1539148801 / 1000000000000000000)) * (126 / 100) +
      2 * (((1539148801 / 1000000000000000000)) ^ 2 + 2 * ((4613521693 / 1000000000000000000)) * ((18496747 / 50000000000000000))) +
      6 * ((1539148801 / 1000000000000000000)) * ((18496747 / 50000000000000000)) * (126 / 100) + 8 * ((18496747 / 50000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12666 162) (d.f1 12666 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12666 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12666 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12666 162) (d.f1 12666 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12666 162) (d.w1 12666 162) (d.w2 12666 162)
  have hwexpr0 : 0 ≤ d.w0 12666 162 + d.w1 12666 162 * √(π / 2) +
      2 * d.w2 12666 162 + energyR16 12666 *
      radiusPolynomialRoot16 (d.w0 12666 162) (d.w1 12666 162) (d.w2 12666 162) := by
    positivity
  constructor
  · change (12666 : ℝ) ^ 8 * (mA 12666 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12666 162) (d.f1 12666 162) d.f2 + locationR16 12666 *
        radiusPolynomialRoot16 (d.f0 12666 162) (d.f1 12666 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12666 : ℝ) ^ 8 * (mA 12666 : ℝ) ^ 8 *
        ((((4613521693 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4613521693 / 1000000000000000000)) * ((1539148801 / 1000000000000000000)) * (126 / 100) +
          2 * (((1539148801 / 1000000000000000000)) ^ 2 + 2 * ((4613521693 / 1000000000000000000)) * ((18496747 / 50000000000000000))) +
          6 * ((1539148801 / 1000000000000000000)) * ((18496747 / 50000000000000000)) * (126 / 100) + 8 * ((18496747 / 50000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12666) *
          (32 * (((4613521693 / 1000000000000000000) : ℝ) + (1539148801 / 1000000000000000000) + (18496747 / 50000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12666 : ℝ) ^ 16 *
      (d.w0 12666 162 + d.w1 12666 162 * √(π / 2) + 2 * d.w2 12666 162 +
        energyR16 12666 * radiusPolynomialRoot16 (d.w0 12666 162) (d.w1 12666 162)
          (d.w2 12666 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12666 : ℝ) ^ 16 *
        (((924001453 / 50000000000000000000) : ℝ) + ((1314818691 / 100000000000000000000)) * (126 / 100) + 2 * ((48040169 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12666) *
          (32 * (((924001453 / 50000000000000000000) : ℝ) + (1314818691 / 100000000000000000000) + (48040169 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12666

/-! A coarse bound on the actual paper statistics constant at dimension 12667. -/
namespace BstLean.Part266.Row12667
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12665 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12665 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12665 128 ≤ (12919 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12919 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12667) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12667 : ℕ))
    (by norm_num : (12667 : ℕ) ≤ 16384)
  have ht : paperTail256 12667 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12667 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12667 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12667 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12667 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12667 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12665 128 * √(2 / (12667 : ℝ)) *
      (√(12667 : ℝ) + paperT0 12667 + paperTail256 12667) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12667 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12667 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12667 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12665 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12665 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12667 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12667

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12667
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12667 (61 / 100) 162 (17 / (100 * 12667)) (26 / (10 * 12667)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12667 (61 / 100) 162 (17 / (100 * 12667)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (240141427 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (189580351 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1044742379 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12667 / 12667 * (61 / 100)) ^ 4 * inverseRadius8 (12667 - 1) /
            envelopeGap 12667 (61 / 100) 162 (17 / (100 * 12667)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12667

namespace BstLean.Part266.Row12667
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12667 162 ≤ (2306304459 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12667 162 ≤ (1538844513 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (184930933 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12667 162 ≤ (923782393 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12667 162 ≤ (1314507083 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12667 162 ≤ (96057583 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (240141427 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (240141427 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (189580351 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1044742379 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3663427 / 1000000000) : ℝ) ≤ √(17 / (100 * 12667) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12667) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1095767829 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38944098501 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12667) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12667) ≤ (55822751 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12667) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12667 * (162 : ℝ) ^ 2 + 26 / (10 * 12667) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12667) : ℝ)) (tA 12667 * 162 ^ 2 + 26 / (10 * 12667)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3663427 / 1000000000))) * ((240141427 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3663427 / 1000000000)) ^ 3) * ((189580351 / 125000000000000000000000))) + ((1044742379 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3663427 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12667) : ℝ)) d.D d.V d.P (√(tA 12667) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3663427 / 1000000000)) ^ 2 * (((1095767829 / 500000000000000)) * ((38944098501 / 1000000000000000000)))) + ((1044742379 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12667) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3663427 / 1000000000)) * ((240141427 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12667) : ℝ)) (tA 12667 * 162 ^ 2 + 26 / (10 * 12667)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((240141427 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3663427 / 1000000000)) ^ 2) * ((189580351 / 125000000000000000000000)) + ((1044742379 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12667) : ℝ)) (√(26 / (10 * 12667) : ℝ)) d.D d.V d.P (√(tA 12667) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3663427 / 1000000000)) * (((1095767829 / 500000000000000)) * ((38944098501 / 1000000000000000000))) + ((1044742379 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12667) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((240141427 / 50000000000000000000) : ℝ) + ((1044742379 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12667

namespace BstLean.Part266.Row12667
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12667 162 ∧
    0 ≤ (tableEnvelope C).f1 12667 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12667 162 ∧
    0 ≤ (tableEnvelope C).w1 12667 162 ∧ 0 ≤ (tableEnvelope C).w2 12667 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12667 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12667 162 ∧ 0 ≤ d.f1 12667 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12667 162 ∧ 0 ≤ d.w1 12667 162 ∧ 0 ≤ d.w2 12667 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12667 ≤ 2 * (228 / 100 : ℝ) / 12667 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12667 ≤ 2 * (370 / 100 : ℝ) / 12667 := by
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
    (completeRAData (tableEnvelope C) 12667 162).locationBound 12667 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12667 162).energyBound 12667 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12667 162) (d.f1 12667 162) d.f2 ≤
      32 * (((2306304459 / 500000000000000000) : ℝ) + (1538844513 / 1000000000000000000) + (184930933 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12667 162) (d.w1 12667 162)
      (d.w2 12667 162) ≤
      32 * (((923782393 / 50000000000000000000) : ℝ) + (1314507083 / 100000000000000000000) + (96057583 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12667 162) (d.f1 12667 162) d.f2 ≤
      ((2306304459 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2306304459 / 500000000000000000)) * ((1538844513 / 1000000000000000000)) * (126 / 100) +
      2 * (((1538844513 / 1000000000000000000)) ^ 2 + 2 * ((2306304459 / 500000000000000000)) * ((184930933 / 500000000000000000))) +
      6 * ((1538844513 / 1000000000000000000)) * ((184930933 / 500000000000000000)) * (126 / 100) + 8 * ((184930933 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12667 162) (d.f1 12667 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12667 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12667 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12667 162) (d.f1 12667 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12667 162) (d.w1 12667 162) (d.w2 12667 162)
  have hwexpr0 : 0 ≤ d.w0 12667 162 + d.w1 12667 162 * √(π / 2) +
      2 * d.w2 12667 162 + energyR16 12667 *
      radiusPolynomialRoot16 (d.w0 12667 162) (d.w1 12667 162) (d.w2 12667 162) := by
    positivity
  constructor
  · change (12667 : ℝ) ^ 8 * (mA 12667 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12667 162) (d.f1 12667 162) d.f2 + locationR16 12667 *
        radiusPolynomialRoot16 (d.f0 12667 162) (d.f1 12667 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12667 : ℝ) ^ 8 * (mA 12667 : ℝ) ^ 8 *
        ((((2306304459 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2306304459 / 500000000000000000)) * ((1538844513 / 1000000000000000000)) * (126 / 100) +
          2 * (((1538844513 / 1000000000000000000)) ^ 2 + 2 * ((2306304459 / 500000000000000000)) * ((184930933 / 500000000000000000))) +
          6 * ((1538844513 / 1000000000000000000)) * ((184930933 / 500000000000000000)) * (126 / 100) + 8 * ((184930933 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12667) *
          (32 * (((2306304459 / 500000000000000000) : ℝ) + (1538844513 / 1000000000000000000) + (184930933 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12667 : ℝ) ^ 16 *
      (d.w0 12667 162 + d.w1 12667 162 * √(π / 2) + 2 * d.w2 12667 162 +
        energyR16 12667 * radiusPolynomialRoot16 (d.w0 12667 162) (d.w1 12667 162)
          (d.w2 12667 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12667 : ℝ) ^ 16 *
        (((923782393 / 50000000000000000000) : ℝ) + ((1314507083 / 100000000000000000000)) * (126 / 100) + 2 * ((96057583 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12667) *
          (32 * (((923782393 / 50000000000000000000) : ℝ) + (1314507083 / 100000000000000000000) + (96057583 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12667

/-! A coarse bound on the actual paper statistics constant at dimension 12668. -/
namespace BstLean.Part266.Row12668
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12666 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12666 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12666 128 ≤ (12920 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12920 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12668) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12668 : ℕ))
    (by norm_num : (12668 : ℕ) ≤ 16384)
  have ht : paperTail256 12668 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12668 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12668 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12668 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12668 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12668 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12666 128 * √(2 / (12668 : ℝ)) *
      (√(12668 : ℝ) + paperT0 12668 + paperTail256 12668) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12668 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12668 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12668 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12666 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12666 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12668 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12668

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12668
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12668 (61 / 100) 163 (17 / (100 * 12668)) (26 / (10 * 12668)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12668 (61 / 100) 163 (17 / (100 * 12668)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (240084559 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (379040989 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5222822453 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12668 / 12668 * (61 / 100)) ^ 4 * inverseRadius8 (12668 - 1) /
            envelopeGap 12668 (61 / 100) 163 (17 / (100 * 12668)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12668

namespace BstLean.Part266.Row12668
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12668 163 ≤ (1152925023 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12668 163 ≤ (384635291 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (73957783 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12668 163 ≤ (1847127563 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12668 163 ≤ (1314195939 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12668 163 ≤ (240087089 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (240084559 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (240084559 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (379040989 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5222822453 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1831641 / 500000000) : ℝ) ≤ √(17 / (100 * 12668) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12668) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1095638077 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1557518003 / 40000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12668) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12668) ≤ (6977293 / 62500000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12668) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12668 * (163 : ℝ) ^ 2 + 26 / (10 * 12668) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12668) : ℝ)) (tA 12668 * 163 ^ 2 + 26 / (10 * 12668)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1831641 / 500000000))) * ((240084559 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1831641 / 500000000)) ^ 3) * ((379040989 / 250000000000000000000000))) + ((5222822453 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1831641 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12668) : ℝ)) d.D d.V d.P (√(tA 12668) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1831641 / 500000000)) ^ 2 * (((1095638077 / 500000000000000)) * ((1557518003 / 40000000000000000)))) + ((5222822453 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12668) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1831641 / 500000000)) * ((240084559 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12668) : ℝ)) (tA 12668 * 163 ^ 2 + 26 / (10 * 12668)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((240084559 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1831641 / 500000000)) ^ 2) * ((379040989 / 250000000000000000000000)) + ((5222822453 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12668) : ℝ)) (√(26 / (10 * 12668) : ℝ)) d.D d.V d.P (√(tA 12668) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1831641 / 500000000)) * (((1095638077 / 500000000000000)) * ((1557518003 / 40000000000000000))) + ((5222822453 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12668) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((240084559 / 50000000000000000000) : ℝ) + ((5222822453 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12668

namespace BstLean.Part266.Row12668
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12668 163 ∧
    0 ≤ (tableEnvelope C).f1 12668 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12668 163 ∧
    0 ≤ (tableEnvelope C).w1 12668 163 ∧ 0 ≤ (tableEnvelope C).w2 12668 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12668 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12668 163 ∧ 0 ≤ d.f1 12668 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12668 163 ∧ 0 ≤ d.w1 12668 163 ∧ 0 ≤ d.w2 12668 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12668 ≤ 2 * (228 / 100 : ℝ) / 12668 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12668 ≤ 2 * (370 / 100 : ℝ) / 12668 := by
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
    (completeRAData (tableEnvelope C) 12668 163).locationBound 12668 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12668 163).energyBound 12668 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12668 163) (d.f1 12668 163) d.f2 ≤
      32 * (((1152925023 / 250000000000000000) : ℝ) + (384635291 / 250000000000000000) + (73957783 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12668 163) (d.w1 12668 163)
      (d.w2 12668 163) ≤
      32 * (((1847127563 / 100000000000000000000) : ℝ) + (1314195939 / 100000000000000000000) + (240087089 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12668 163) (d.f1 12668 163) d.f2 ≤
      ((1152925023 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1152925023 / 250000000000000000)) * ((384635291 / 250000000000000000)) * (126 / 100) +
      2 * (((384635291 / 250000000000000000)) ^ 2 + 2 * ((1152925023 / 250000000000000000)) * ((73957783 / 200000000000000000))) +
      6 * ((384635291 / 250000000000000000)) * ((73957783 / 200000000000000000)) * (126 / 100) + 8 * ((73957783 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12668 163) (d.f1 12668 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12668 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12668 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12668 163) (d.f1 12668 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12668 163) (d.w1 12668 163) (d.w2 12668 163)
  have hwexpr0 : 0 ≤ d.w0 12668 163 + d.w1 12668 163 * √(π / 2) +
      2 * d.w2 12668 163 + energyR16 12668 *
      radiusPolynomialRoot16 (d.w0 12668 163) (d.w1 12668 163) (d.w2 12668 163) := by
    positivity
  constructor
  · change (12668 : ℝ) ^ 8 * (mA 12668 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12668 163) (d.f1 12668 163) d.f2 + locationR16 12668 *
        radiusPolynomialRoot16 (d.f0 12668 163) (d.f1 12668 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12668 : ℝ) ^ 8 * (mA 12668 : ℝ) ^ 8 *
        ((((1152925023 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1152925023 / 250000000000000000)) * ((384635291 / 250000000000000000)) * (126 / 100) +
          2 * (((384635291 / 250000000000000000)) ^ 2 + 2 * ((1152925023 / 250000000000000000)) * ((73957783 / 200000000000000000))) +
          6 * ((384635291 / 250000000000000000)) * ((73957783 / 200000000000000000)) * (126 / 100) + 8 * ((73957783 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12668) *
          (32 * (((1152925023 / 250000000000000000) : ℝ) + (384635291 / 250000000000000000) + (73957783 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12668 : ℝ) ^ 16 *
      (d.w0 12668 163 + d.w1 12668 163 * √(π / 2) + 2 * d.w2 12668 163 +
        energyR16 12668 * radiusPolynomialRoot16 (d.w0 12668 163) (d.w1 12668 163)
          (d.w2 12668 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12668 : ℝ) ^ 16 *
        (((1847127563 / 100000000000000000000) : ℝ) + ((1314195939 / 100000000000000000000)) * (126 / 100) + 2 * ((240087089 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12668) *
          (32 * (((1847127563 / 100000000000000000000) : ℝ) + (1314195939 / 100000000000000000000) + (240087089 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12668

/-! A coarse bound on the actual paper statistics constant at dimension 12669. -/
namespace BstLean.Part266.Row12669
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12667 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12667 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12667 128 ≤ (12921 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12921 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12669) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12669 : ℕ))
    (by norm_num : (12669 : ℕ) ≤ 16384)
  have ht : paperTail256 12669 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12669 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12669 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12669 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12669 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12669 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12667 128 * √(2 / (12669 : ℝ)) *
      (√(12669 : ℝ) + paperT0 12669 + paperTail256 12669) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12669 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12669 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12669 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12667 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12667 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12669 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12669

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12669
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12669 (61 / 100) 163 (17 / (100 * 12669)) (26 / (10 * 12669)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12669 (61 / 100) 163 (17 / (100 * 12669)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (240027709 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (757842647 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2609746541 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12669 / 12669 * (61 / 100)) ^ 4 * inverseRadius8 (12669 - 1) /
            envelopeGap 12669 (61 / 100) 163 (17 / (100 * 12669)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12669

namespace BstLean.Part266.Row12669
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12669 163 ≤ (4610787949 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12669 163 ≤ (1538237073 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (184857943 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12669 163 ≤ (923344873 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12669 163 ≤ (65694227 / 5000000000000000000)
  w2 : (tableEnvelope C).w2 12669 163 ≤ (19202419 / 4000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (240027709 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (240027709 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (757842647 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2609746541 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1831569 / 500000000) : ℝ) ≤ √(17 / (100 * 12669) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12669) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2191016701 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19465901559 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12669) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12669) ≤ (111627877 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12669) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12669 * (163 : ℝ) ^ 2 + 26 / (10 * 12669) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12669) : ℝ)) (tA 12669 * 163 ^ 2 + 26 / (10 * 12669)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1831569 / 500000000))) * ((240027709 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1831569 / 500000000)) ^ 3) * ((757842647 / 500000000000000000000000))) + ((2609746541 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1831569 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12669) : ℝ)) d.D d.V d.P (√(tA 12669) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1831569 / 500000000)) ^ 2 * (((2191016701 / 1000000000000000)) * ((19465901559 / 500000000000000000)))) + ((2609746541 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12669) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1831569 / 500000000)) * ((240027709 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12669) : ℝ)) (tA 12669 * 163 ^ 2 + 26 / (10 * 12669)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((240027709 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1831569 / 500000000)) ^ 2) * ((757842647 / 500000000000000000000000)) + ((2609746541 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12669) : ℝ)) (√(26 / (10 * 12669) : ℝ)) d.D d.V d.P (√(tA 12669) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1831569 / 500000000)) * (((2191016701 / 1000000000000000)) * ((19465901559 / 500000000000000000))) + ((2609746541 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12669) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((240027709 / 50000000000000000000) : ℝ) + ((2609746541 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12669

namespace BstLean.Part266.Row12669
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12669 163 ∧
    0 ≤ (tableEnvelope C).f1 12669 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12669 163 ∧
    0 ≤ (tableEnvelope C).w1 12669 163 ∧ 0 ≤ (tableEnvelope C).w2 12669 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12669 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12669 163 ∧ 0 ≤ d.f1 12669 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12669 163 ∧ 0 ≤ d.w1 12669 163 ∧ 0 ≤ d.w2 12669 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12669 ≤ 2 * (228 / 100 : ℝ) / 12669 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12669 ≤ 2 * (370 / 100 : ℝ) / 12669 := by
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
    (completeRAData (tableEnvelope C) 12669 163).locationBound 12669 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12669 163).energyBound 12669 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12669 163) (d.f1 12669 163) d.f2 ≤
      32 * (((4610787949 / 1000000000000000000) : ℝ) + (1538237073 / 1000000000000000000) + (184857943 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12669 163) (d.w1 12669 163)
      (d.w2 12669 163) ≤
      32 * (((923344873 / 50000000000000000000) : ℝ) + (65694227 / 5000000000000000000) + (19202419 / 4000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12669 163) (d.f1 12669 163) d.f2 ≤
      ((4610787949 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4610787949 / 1000000000000000000)) * ((1538237073 / 1000000000000000000)) * (126 / 100) +
      2 * (((1538237073 / 1000000000000000000)) ^ 2 + 2 * ((4610787949 / 1000000000000000000)) * ((184857943 / 500000000000000000))) +
      6 * ((1538237073 / 1000000000000000000)) * ((184857943 / 500000000000000000)) * (126 / 100) + 8 * ((184857943 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12669 163) (d.f1 12669 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12669 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12669 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12669 163) (d.f1 12669 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12669 163) (d.w1 12669 163) (d.w2 12669 163)
  have hwexpr0 : 0 ≤ d.w0 12669 163 + d.w1 12669 163 * √(π / 2) +
      2 * d.w2 12669 163 + energyR16 12669 *
      radiusPolynomialRoot16 (d.w0 12669 163) (d.w1 12669 163) (d.w2 12669 163) := by
    positivity
  constructor
  · change (12669 : ℝ) ^ 8 * (mA 12669 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12669 163) (d.f1 12669 163) d.f2 + locationR16 12669 *
        radiusPolynomialRoot16 (d.f0 12669 163) (d.f1 12669 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12669 : ℝ) ^ 8 * (mA 12669 : ℝ) ^ 8 *
        ((((4610787949 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4610787949 / 1000000000000000000)) * ((1538237073 / 1000000000000000000)) * (126 / 100) +
          2 * (((1538237073 / 1000000000000000000)) ^ 2 + 2 * ((4610787949 / 1000000000000000000)) * ((184857943 / 500000000000000000))) +
          6 * ((1538237073 / 1000000000000000000)) * ((184857943 / 500000000000000000)) * (126 / 100) + 8 * ((184857943 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12669) *
          (32 * (((4610787949 / 1000000000000000000) : ℝ) + (1538237073 / 1000000000000000000) + (184857943 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12669 : ℝ) ^ 16 *
      (d.w0 12669 163 + d.w1 12669 163 * √(π / 2) + 2 * d.w2 12669 163 +
        energyR16 12669 * radiusPolynomialRoot16 (d.w0 12669 163) (d.w1 12669 163)
          (d.w2 12669 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12669 : ℝ) ^ 16 *
        (((923344873 / 50000000000000000000) : ℝ) + ((65694227 / 5000000000000000000)) * (126 / 100) + 2 * ((19202419 / 4000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12669) *
          (32 * (((923344873 / 50000000000000000000) : ℝ) + (65694227 / 5000000000000000000) + (19202419 / 4000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12669

/-! A coarse bound on the actual paper statistics constant at dimension 12670. -/
namespace BstLean.Part266.Row12670
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12668 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12668 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12668 128 ≤ (12922 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12922 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12670) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12670 : ℕ))
    (by norm_num : (12670 : ℕ) ≤ 16384)
  have ht : paperTail256 12670 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12670 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12670 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12670 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12670 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12670 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12668 128 * √(2 / (12670 : ℝ)) *
      (√(12670 : ℝ) + paperT0 12670 + paperTail256 12670) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12670 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12670 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12670 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12668 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12668 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12670 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12670

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12670
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12670 (61 / 100) 163 (17 / (100 * 12670)) (26 / (10 * 12670)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12670 (61 / 100) 163 (17 / (100 * 12670)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (479941753 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (75760341 / 50000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5216166101 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12670 / 12670 * (61 / 100)) ^ 4 * inverseRadius8 (12670 - 1) /
            envelopeGap 12670 (61 / 100) 163 (17 / (100 * 12670)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12670

namespace BstLean.Part266.Row12670
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12670 163 ≤ (4609879749 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12670 163 ≤ (768966959 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (184821489 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12670 163 ≤ (230781603 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 12670 163 ≤ (1313573603 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12670 163 ≤ (239973403 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (479941753 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (479941753 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (75760341 / 50000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5216166101 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3662993 / 1000000000) : ℝ) ≤ √(17 / (100 * 12670) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12670) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2190757297 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19462828803 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12670) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12670) ≤ (55809533 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12670) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12670 * (163 : ℝ) ^ 2 + 26 / (10 * 12670) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12670) : ℝ)) (tA 12670 * 163 ^ 2 + 26 / (10 * 12670)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3662993 / 1000000000))) * ((479941753 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3662993 / 1000000000)) ^ 3) * ((75760341 / 50000000000000000000000))) + ((5216166101 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3662993 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12670) : ℝ)) d.D d.V d.P (√(tA 12670) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3662993 / 1000000000)) ^ 2 * (((2190757297 / 1000000000000000)) * ((19462828803 / 500000000000000000)))) + ((5216166101 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12670) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3662993 / 1000000000)) * ((479941753 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12670) : ℝ)) (tA 12670 * 163 ^ 2 + 26 / (10 * 12670)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((479941753 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3662993 / 1000000000)) ^ 2) * ((75760341 / 50000000000000000000000)) + ((5216166101 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12670) : ℝ)) (√(26 / (10 * 12670) : ℝ)) d.D d.V d.P (√(tA 12670) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3662993 / 1000000000)) * (((2190757297 / 1000000000000000)) * ((19462828803 / 500000000000000000))) + ((5216166101 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12670) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((479941753 / 100000000000000000000) : ℝ) + ((5216166101 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12670

namespace BstLean.Part266.Row12670
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12670 163 ∧
    0 ≤ (tableEnvelope C).f1 12670 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12670 163 ∧
    0 ≤ (tableEnvelope C).w1 12670 163 ∧ 0 ≤ (tableEnvelope C).w2 12670 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12670 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12670 163 ∧ 0 ≤ d.f1 12670 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12670 163 ∧ 0 ≤ d.w1 12670 163 ∧ 0 ≤ d.w2 12670 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12670 ≤ 2 * (228 / 100 : ℝ) / 12670 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12670 ≤ 2 * (370 / 100 : ℝ) / 12670 := by
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
    (completeRAData (tableEnvelope C) 12670 163).locationBound 12670 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12670 163).energyBound 12670 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12670 163) (d.f1 12670 163) d.f2 ≤
      32 * (((4609879749 / 1000000000000000000) : ℝ) + (768966959 / 500000000000000000) + (184821489 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12670 163) (d.w1 12670 163)
      (d.w2 12670 163) ≤
      32 * (((230781603 / 12500000000000000000) : ℝ) + (1313573603 / 100000000000000000000) + (239973403 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12670 163) (d.f1 12670 163) d.f2 ≤
      ((4609879749 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4609879749 / 1000000000000000000)) * ((768966959 / 500000000000000000)) * (126 / 100) +
      2 * (((768966959 / 500000000000000000)) ^ 2 + 2 * ((4609879749 / 1000000000000000000)) * ((184821489 / 500000000000000000))) +
      6 * ((768966959 / 500000000000000000)) * ((184821489 / 500000000000000000)) * (126 / 100) + 8 * ((184821489 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12670 163) (d.f1 12670 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12670 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12670 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12670 163) (d.f1 12670 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12670 163) (d.w1 12670 163) (d.w2 12670 163)
  have hwexpr0 : 0 ≤ d.w0 12670 163 + d.w1 12670 163 * √(π / 2) +
      2 * d.w2 12670 163 + energyR16 12670 *
      radiusPolynomialRoot16 (d.w0 12670 163) (d.w1 12670 163) (d.w2 12670 163) := by
    positivity
  constructor
  · change (12670 : ℝ) ^ 8 * (mA 12670 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12670 163) (d.f1 12670 163) d.f2 + locationR16 12670 *
        radiusPolynomialRoot16 (d.f0 12670 163) (d.f1 12670 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12670 : ℝ) ^ 8 * (mA 12670 : ℝ) ^ 8 *
        ((((4609879749 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4609879749 / 1000000000000000000)) * ((768966959 / 500000000000000000)) * (126 / 100) +
          2 * (((768966959 / 500000000000000000)) ^ 2 + 2 * ((4609879749 / 1000000000000000000)) * ((184821489 / 500000000000000000))) +
          6 * ((768966959 / 500000000000000000)) * ((184821489 / 500000000000000000)) * (126 / 100) + 8 * ((184821489 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12670) *
          (32 * (((4609879749 / 1000000000000000000) : ℝ) + (768966959 / 500000000000000000) + (184821489 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12670 : ℝ) ^ 16 *
      (d.w0 12670 163 + d.w1 12670 163 * √(π / 2) + 2 * d.w2 12670 163 +
        energyR16 12670 * radiusPolynomialRoot16 (d.w0 12670 163) (d.w1 12670 163)
          (d.w2 12670 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12670 : ℝ) ^ 16 *
        (((230781603 / 12500000000000000000) : ℝ) + ((1313573603 / 100000000000000000000)) * (126 / 100) + 2 * ((239973403 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12670) *
          (32 * (((230781603 / 12500000000000000000) : ℝ) + (1313573603 / 100000000000000000000) + (239973403 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12670

/-! A coarse bound on the actual paper statistics constant at dimension 12671. -/
namespace BstLean.Part266.Row12671
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12669 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12669 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12669 128 ≤ (12923 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12923 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12671) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12671 : ℕ))
    (by norm_num : (12671 : ℕ) ≤ 16384)
  have ht : paperTail256 12671 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12671 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12671 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12671 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12671 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12671 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12669 128 * √(2 / (12671 : ℝ)) *
      (√(12671 : ℝ) + paperT0 12671 + paperTail256 12671) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12671 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12671 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12671 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12669 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12669 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12671 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12671

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12671
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12671 (61 / 100) 163 (17 / (100 * 12671)) (26 / (10 * 12671)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12671 (61 / 100) 163 (17 / (100 * 12671)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (30709 / 6400000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (302945707 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5212841507 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12671 / 12671 * (61 / 100)) ^ 4 * inverseRadius8 (12671 - 1) /
            envelopeGap 12671 (61 / 100) 163 (17 / (100 * 12671)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12671

namespace BstLean.Part266.Row12671
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12671 163 ≤ (576121483 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12671 163 ≤ (1537630863 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (369570093 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12671 163 ≤ (922908027 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12671 163 ≤ (1313262771 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12671 163 ≤ (19193327 / 4000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (30709 / 6400000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (30709 / 6400000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (302945707 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5212841507 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((7154 / 1953125) : ℝ) ≤ √(17 / (100 * 12671) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12671) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1095248973 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38919513551 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12671) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12671) ≤ (111610257 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12671) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12671 * (163 : ℝ) ^ 2 + 26 / (10 * 12671) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12671) : ℝ)) (tA 12671 * 163 ^ 2 + 26 / (10 * 12671)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((7154 / 1953125))) * ((30709 / 6400000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((7154 / 1953125)) ^ 3) * ((302945707 / 200000000000000000000000))) + ((5212841507 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((7154 / 1953125)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12671) : ℝ)) d.D d.V d.P (√(tA 12671) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((7154 / 1953125)) ^ 2 * (((1095248973 / 500000000000000)) * ((38919513551 / 1000000000000000000)))) + ((5212841507 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12671) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((7154 / 1953125)) * ((30709 / 6400000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12671) : ℝ)) (tA 12671 * 163 ^ 2 + 26 / (10 * 12671)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((30709 / 6400000000000000) : ℝ) + (24198 / 100000) / (2 * ((7154 / 1953125)) ^ 2) * ((302945707 / 200000000000000000000000)) + ((5212841507 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12671) : ℝ)) (√(26 / (10 * 12671) : ℝ)) d.D d.V d.P (√(tA 12671) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((7154 / 1953125)) * (((1095248973 / 500000000000000)) * ((38919513551 / 1000000000000000000))) + ((5212841507 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12671) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((30709 / 6400000000000000) : ℝ) + ((5212841507 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12671

namespace BstLean.Part266.Row12671
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12671 163 ∧
    0 ≤ (tableEnvelope C).f1 12671 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12671 163 ∧
    0 ≤ (tableEnvelope C).w1 12671 163 ∧ 0 ≤ (tableEnvelope C).w2 12671 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12671 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12671 163 ∧ 0 ≤ d.f1 12671 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12671 163 ∧ 0 ≤ d.w1 12671 163 ∧ 0 ≤ d.w2 12671 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12671 ≤ 2 * (228 / 100 : ℝ) / 12671 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12671 ≤ 2 * (370 / 100 : ℝ) / 12671 := by
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
    (completeRAData (tableEnvelope C) 12671 163).locationBound 12671 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12671 163).energyBound 12671 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12671 163) (d.f1 12671 163) d.f2 ≤
      32 * (((576121483 / 125000000000000000) : ℝ) + (1537630863 / 1000000000000000000) + (369570093 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12671 163) (d.w1 12671 163)
      (d.w2 12671 163) ≤
      32 * (((922908027 / 50000000000000000000) : ℝ) + (1313262771 / 100000000000000000000) + (19193327 / 4000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12671 163) (d.f1 12671 163) d.f2 ≤
      ((576121483 / 125000000000000000) : ℝ) ^ 2 + 2 * ((576121483 / 125000000000000000)) * ((1537630863 / 1000000000000000000)) * (126 / 100) +
      2 * (((1537630863 / 1000000000000000000)) ^ 2 + 2 * ((576121483 / 125000000000000000)) * ((369570093 / 1000000000000000000))) +
      6 * ((1537630863 / 1000000000000000000)) * ((369570093 / 1000000000000000000)) * (126 / 100) + 8 * ((369570093 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12671 163) (d.f1 12671 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12671 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12671 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12671 163) (d.f1 12671 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12671 163) (d.w1 12671 163) (d.w2 12671 163)
  have hwexpr0 : 0 ≤ d.w0 12671 163 + d.w1 12671 163 * √(π / 2) +
      2 * d.w2 12671 163 + energyR16 12671 *
      radiusPolynomialRoot16 (d.w0 12671 163) (d.w1 12671 163) (d.w2 12671 163) := by
    positivity
  constructor
  · change (12671 : ℝ) ^ 8 * (mA 12671 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12671 163) (d.f1 12671 163) d.f2 + locationR16 12671 *
        radiusPolynomialRoot16 (d.f0 12671 163) (d.f1 12671 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12671 : ℝ) ^ 8 * (mA 12671 : ℝ) ^ 8 *
        ((((576121483 / 125000000000000000) : ℝ) ^ 2 + 2 * ((576121483 / 125000000000000000)) * ((1537630863 / 1000000000000000000)) * (126 / 100) +
          2 * (((1537630863 / 1000000000000000000)) ^ 2 + 2 * ((576121483 / 125000000000000000)) * ((369570093 / 1000000000000000000))) +
          6 * ((1537630863 / 1000000000000000000)) * ((369570093 / 1000000000000000000)) * (126 / 100) + 8 * ((369570093 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12671) *
          (32 * (((576121483 / 125000000000000000) : ℝ) + (1537630863 / 1000000000000000000) + (369570093 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12671 : ℝ) ^ 16 *
      (d.w0 12671 163 + d.w1 12671 163 * √(π / 2) + 2 * d.w2 12671 163 +
        energyR16 12671 * radiusPolynomialRoot16 (d.w0 12671 163) (d.w1 12671 163)
          (d.w2 12671 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12671 : ℝ) ^ 16 *
        (((922908027 / 50000000000000000000) : ℝ) + ((1313262771 / 100000000000000000000)) * (126 / 100) + 2 * ((19193327 / 4000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12671) *
          (32 * (((922908027 / 50000000000000000000) : ℝ) + (1313262771 / 100000000000000000000) + (19193327 / 4000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12671

/-! A coarse bound on the actual paper statistics constant at dimension 12672. -/
namespace BstLean.Part266.Row12672
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12670 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12670 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12670 128 ≤ (12924 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12924 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12672) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12672 : ℕ))
    (by norm_num : (12672 : ℕ) ≤ 16384)
  have ht : paperTail256 12672 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12672 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12672 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12672 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12672 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12672 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12670 128 * √(2 / (12672 : ℝ)) *
      (√(12672 : ℝ) + paperT0 12672 + paperTail256 12672) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12672 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12672 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12672 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12670 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12670 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12672 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12672

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12672
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12672 (61 / 100) 163 (17 / (100 * 12672)) (26 / (10 * 12672)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12672 (61 / 100) 163 (17 / (100 * 12672)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (119928633 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1514250439 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (52095193 / 10000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12672 / 12672 * (61 / 100)) ^ 4 * inverseRadius8 (12672 - 1) /
            envelopeGap 12672 (61 / 100) 163 (17 / (100 * 12672)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12672

namespace BstLean.Part266.Row12672
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12672 163 ≤ (230403033 / 50000000000000000)
  f1 : (tableEnvelope C).f1 12672 163 ≤ (768663533 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (369497129 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12672 163 ≤ (14417021 / 781250000000000000)
  w1 : (tableEnvelope C).w1 12672 163 ≤ (328237921 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12672 163 ≤ (479719579 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (119928633 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (119928633 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1514250439 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (52095193 / 10000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((228919 / 62500000) : ℝ) ≤ √(17 / (100 * 12672) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12672) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (438047729 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19456685477 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12672) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12672) ≤ (2232029 / 20000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12672) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12672 * (163 : ℝ) ^ 2 + 26 / (10 * 12672) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12672) : ℝ)) (tA 12672 * 163 ^ 2 + 26 / (10 * 12672)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((228919 / 62500000))) * ((119928633 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((228919 / 62500000)) ^ 3) * ((1514250439 / 1000000000000000000000000))) + ((52095193 / 10000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((228919 / 62500000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12672) : ℝ)) d.D d.V d.P (√(tA 12672) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((228919 / 62500000)) ^ 2 * (((438047729 / 200000000000000)) * ((19456685477 / 500000000000000000)))) + ((52095193 / 10000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12672) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((228919 / 62500000)) * ((119928633 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12672) : ℝ)) (tA 12672 * 163 ^ 2 + 26 / (10 * 12672)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((119928633 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((228919 / 62500000)) ^ 2) * ((1514250439 / 1000000000000000000000000)) + ((52095193 / 10000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12672) : ℝ)) (√(26 / (10 * 12672) : ℝ)) d.D d.V d.P (√(tA 12672) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((228919 / 62500000)) * (((438047729 / 200000000000000)) * ((19456685477 / 500000000000000000))) + ((52095193 / 10000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12672) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((119928633 / 25000000000000000000) : ℝ) + ((52095193 / 10000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12672

namespace BstLean.Part266.Row12672
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12672 163 ∧
    0 ≤ (tableEnvelope C).f1 12672 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12672 163 ∧
    0 ≤ (tableEnvelope C).w1 12672 163 ∧ 0 ≤ (tableEnvelope C).w2 12672 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12672 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12672 163 ∧ 0 ≤ d.f1 12672 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12672 163 ∧ 0 ≤ d.w1 12672 163 ∧ 0 ≤ d.w2 12672 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12672 ≤ 2 * (228 / 100 : ℝ) / 12672 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12672 ≤ 2 * (370 / 100 : ℝ) / 12672 := by
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
    (completeRAData (tableEnvelope C) 12672 163).locationBound 12672 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12672 163).energyBound 12672 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12672 163) (d.f1 12672 163) d.f2 ≤
      32 * (((230403033 / 50000000000000000) : ℝ) + (768663533 / 500000000000000000) + (369497129 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12672 163) (d.w1 12672 163)
      (d.w2 12672 163) ≤
      32 * (((14417021 / 781250000000000000) : ℝ) + (328237921 / 25000000000000000000) + (479719579 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12672 163) (d.f1 12672 163) d.f2 ≤
      ((230403033 / 50000000000000000) : ℝ) ^ 2 + 2 * ((230403033 / 50000000000000000)) * ((768663533 / 500000000000000000)) * (126 / 100) +
      2 * (((768663533 / 500000000000000000)) ^ 2 + 2 * ((230403033 / 50000000000000000)) * ((369497129 / 1000000000000000000))) +
      6 * ((768663533 / 500000000000000000)) * ((369497129 / 1000000000000000000)) * (126 / 100) + 8 * ((369497129 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12672 163) (d.f1 12672 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12672 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12672 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12672 163) (d.f1 12672 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12672 163) (d.w1 12672 163) (d.w2 12672 163)
  have hwexpr0 : 0 ≤ d.w0 12672 163 + d.w1 12672 163 * √(π / 2) +
      2 * d.w2 12672 163 + energyR16 12672 *
      radiusPolynomialRoot16 (d.w0 12672 163) (d.w1 12672 163) (d.w2 12672 163) := by
    positivity
  constructor
  · change (12672 : ℝ) ^ 8 * (mA 12672 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12672 163) (d.f1 12672 163) d.f2 + locationR16 12672 *
        radiusPolynomialRoot16 (d.f0 12672 163) (d.f1 12672 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12672 : ℝ) ^ 8 * (mA 12672 : ℝ) ^ 8 *
        ((((230403033 / 50000000000000000) : ℝ) ^ 2 + 2 * ((230403033 / 50000000000000000)) * ((768663533 / 500000000000000000)) * (126 / 100) +
          2 * (((768663533 / 500000000000000000)) ^ 2 + 2 * ((230403033 / 50000000000000000)) * ((369497129 / 1000000000000000000))) +
          6 * ((768663533 / 500000000000000000)) * ((369497129 / 1000000000000000000)) * (126 / 100) + 8 * ((369497129 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12672) *
          (32 * (((230403033 / 50000000000000000) : ℝ) + (768663533 / 500000000000000000) + (369497129 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12672 : ℝ) ^ 16 *
      (d.w0 12672 163 + d.w1 12672 163 * √(π / 2) + 2 * d.w2 12672 163 +
        energyR16 12672 * radiusPolynomialRoot16 (d.w0 12672 163) (d.w1 12672 163)
          (d.w2 12672 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12672 : ℝ) ^ 16 *
        (((14417021 / 781250000000000000) : ℝ) + ((328237921 / 25000000000000000000)) * (126 / 100) + 2 * ((479719579 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12672) *
          (32 * (((14417021 / 781250000000000000) : ℝ) + (328237921 / 25000000000000000000) + (479719579 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12672

/-! A coarse bound on the actual paper statistics constant at dimension 12673. -/
namespace BstLean.Part266.Row12673
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12671 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12671 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12671 128 ≤ (12925 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12925 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12673) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12673 : ℕ))
    (by norm_num : (12673 : ℕ) ≤ 16384)
  have ht : paperTail256 12673 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12673 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12673 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12673 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12673 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12673 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12671 128 * √(2 / (12673 : ℝ)) *
      (√(12673 : ℝ) + paperT0 12673 + paperTail256 12673) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12673 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12673 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12673 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12671 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12671 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12673 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12673

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12673
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12673 (61 / 100) 163 (17 / (100 * 12673)) (26 / (10 * 12673)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12673 (61 / 100) 163 (17 / (100 * 12673)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (19184039 / 4000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1513772531 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5206199477 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12673 / 12673 * (61 / 100)) ^ 4 * inverseRadius8 (12673 - 1) /
            envelopeGap 12673 (61 / 100) 163 (17 / (100 * 12673)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12673

namespace BstLean.Part266.Row12673
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12673 163 ≤ (23035767 / 5000000000000000)
  f1 : (tableEnvelope C).f1 12673 163 ≤ (1537024207 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (369424287 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12673 163 ≤ (922471109 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12673 163 ≤ (65632053 / 5000000000000000000)
  w2 : (tableEnvelope C).w2 12673 163 ≤ (479606019 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (19184039 / 4000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (19184039 / 4000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1513772531 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5206199477 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3662559 / 1000000000) : ℝ) ≤ √(17 / (100 * 12673) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12673) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (437995879 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9726807451 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12673) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12673) ≤ (111592643 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12673) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12673 * (163 : ℝ) ^ 2 + 26 / (10 * 12673) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12673) : ℝ)) (tA 12673 * 163 ^ 2 + 26 / (10 * 12673)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3662559 / 1000000000))) * ((19184039 / 4000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3662559 / 1000000000)) ^ 3) * ((1513772531 / 1000000000000000000000000))) + ((5206199477 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3662559 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12673) : ℝ)) d.D d.V d.P (√(tA 12673) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3662559 / 1000000000)) ^ 2 * (((437995879 / 200000000000000)) * ((9726807451 / 250000000000000000)))) + ((5206199477 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12673) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3662559 / 1000000000)) * ((19184039 / 4000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12673) : ℝ)) (tA 12673 * 163 ^ 2 + 26 / (10 * 12673)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((19184039 / 4000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3662559 / 1000000000)) ^ 2) * ((1513772531 / 1000000000000000000000000)) + ((5206199477 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12673) : ℝ)) (√(26 / (10 * 12673) : ℝ)) d.D d.V d.P (√(tA 12673) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3662559 / 1000000000)) * (((437995879 / 200000000000000)) * ((9726807451 / 250000000000000000))) + ((5206199477 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12673) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((19184039 / 4000000000000000000) : ℝ) + ((5206199477 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12673

namespace BstLean.Part266.Row12673
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12673 163 ∧
    0 ≤ (tableEnvelope C).f1 12673 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12673 163 ∧
    0 ≤ (tableEnvelope C).w1 12673 163 ∧ 0 ≤ (tableEnvelope C).w2 12673 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12673 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12673 163 ∧ 0 ≤ d.f1 12673 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12673 163 ∧ 0 ≤ d.w1 12673 163 ∧ 0 ≤ d.w2 12673 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12673 ≤ 2 * (228 / 100 : ℝ) / 12673 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12673 ≤ 2 * (370 / 100 : ℝ) / 12673 := by
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
    (completeRAData (tableEnvelope C) 12673 163).locationBound 12673 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12673 163).energyBound 12673 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12673 163) (d.f1 12673 163) d.f2 ≤
      32 * (((23035767 / 5000000000000000) : ℝ) + (1537024207 / 1000000000000000000) + (369424287 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12673 163) (d.w1 12673 163)
      (d.w2 12673 163) ≤
      32 * (((922471109 / 50000000000000000000) : ℝ) + (65632053 / 5000000000000000000) + (479606019 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12673 163) (d.f1 12673 163) d.f2 ≤
      ((23035767 / 5000000000000000) : ℝ) ^ 2 + 2 * ((23035767 / 5000000000000000)) * ((1537024207 / 1000000000000000000)) * (126 / 100) +
      2 * (((1537024207 / 1000000000000000000)) ^ 2 + 2 * ((23035767 / 5000000000000000)) * ((369424287 / 1000000000000000000))) +
      6 * ((1537024207 / 1000000000000000000)) * ((369424287 / 1000000000000000000)) * (126 / 100) + 8 * ((369424287 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12673 163) (d.f1 12673 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12673 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12673 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12673 163) (d.f1 12673 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12673 163) (d.w1 12673 163) (d.w2 12673 163)
  have hwexpr0 : 0 ≤ d.w0 12673 163 + d.w1 12673 163 * √(π / 2) +
      2 * d.w2 12673 163 + energyR16 12673 *
      radiusPolynomialRoot16 (d.w0 12673 163) (d.w1 12673 163) (d.w2 12673 163) := by
    positivity
  constructor
  · change (12673 : ℝ) ^ 8 * (mA 12673 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12673 163) (d.f1 12673 163) d.f2 + locationR16 12673 *
        radiusPolynomialRoot16 (d.f0 12673 163) (d.f1 12673 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12673 : ℝ) ^ 8 * (mA 12673 : ℝ) ^ 8 *
        ((((23035767 / 5000000000000000) : ℝ) ^ 2 + 2 * ((23035767 / 5000000000000000)) * ((1537024207 / 1000000000000000000)) * (126 / 100) +
          2 * (((1537024207 / 1000000000000000000)) ^ 2 + 2 * ((23035767 / 5000000000000000)) * ((369424287 / 1000000000000000000))) +
          6 * ((1537024207 / 1000000000000000000)) * ((369424287 / 1000000000000000000)) * (126 / 100) + 8 * ((369424287 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12673) *
          (32 * (((23035767 / 5000000000000000) : ℝ) + (1537024207 / 1000000000000000000) + (369424287 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12673 : ℝ) ^ 16 *
      (d.w0 12673 163 + d.w1 12673 163 * √(π / 2) + 2 * d.w2 12673 163 +
        energyR16 12673 * radiusPolynomialRoot16 (d.w0 12673 163) (d.w1 12673 163)
          (d.w2 12673 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12673 : ℝ) ^ 16 *
        (((922471109 / 50000000000000000000) : ℝ) + ((65632053 / 5000000000000000000)) * (126 / 100) + 2 * ((479606019 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12673) *
          (32 * (((922471109 / 50000000000000000000) : ℝ) + (65632053 / 5000000000000000000) + (479606019 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12673

/-! A coarse bound on the actual paper statistics constant at dimension 12674. -/
namespace BstLean.Part266.Row12674
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12672 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12672 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12672 128 ≤ (12926 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12926 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12674) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12674 : ℕ))
    (by norm_num : (12674 : ℕ) ≤ 16384)
  have ht : paperTail256 12674 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12674 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12674 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12674 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12674 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12674 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12672 128 * √(2 / (12674 : ℝ)) *
      (√(12674 : ℝ) + paperT0 12674 + paperTail256 12674) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12674 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12674 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12674 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12672 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12672 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12674 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12674

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12674
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12674 (61 / 100) 163 (17 / (100 * 12674)) (26 / (10 * 12674)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12674 (61 / 100) 163 (17 / (100 * 12674)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (239743727 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (378323703 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5202882037 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12674 / 12674 * (61 / 100)) ^ 4 * inverseRadius8 (12674 - 1) /
            envelopeGap 12674 (61 / 100) 163 (17 / (100 * 12674)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12674

namespace BstLean.Part266.Row12674
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12674 163 ≤ (4606242823 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12674 163 ≤ (768360303 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (184675683 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12674 163 ≤ (922252577 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12674 163 ≤ (656165091 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12674 163 ≤ (239746247 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (239743727 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (239743727 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (378323703 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5202882037 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((732483 / 200000000) : ℝ) ≤ √(17 / (100 * 12674) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12674) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2189720197 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19450545057 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12674) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12674) ≤ (55791919 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12674) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12674 * (163 : ℝ) ^ 2 + 26 / (10 * 12674) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12674) : ℝ)) (tA 12674 * 163 ^ 2 + 26 / (10 * 12674)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((732483 / 200000000))) * ((239743727 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((732483 / 200000000)) ^ 3) * ((378323703 / 250000000000000000000000))) + ((5202882037 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((732483 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12674) : ℝ)) d.D d.V d.P (√(tA 12674) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((732483 / 200000000)) ^ 2 * (((2189720197 / 1000000000000000)) * ((19450545057 / 500000000000000000)))) + ((5202882037 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12674) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((732483 / 200000000)) * ((239743727 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12674) : ℝ)) (tA 12674 * 163 ^ 2 + 26 / (10 * 12674)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((239743727 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((732483 / 200000000)) ^ 2) * ((378323703 / 250000000000000000000000)) + ((5202882037 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12674) : ℝ)) (√(26 / (10 * 12674) : ℝ)) d.D d.V d.P (√(tA 12674) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((732483 / 200000000)) * (((2189720197 / 1000000000000000)) * ((19450545057 / 500000000000000000))) + ((5202882037 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12674) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((239743727 / 50000000000000000000) : ℝ) + ((5202882037 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12674

namespace BstLean.Part266.Row12674
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12674 163 ∧
    0 ≤ (tableEnvelope C).f1 12674 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12674 163 ∧
    0 ≤ (tableEnvelope C).w1 12674 163 ∧ 0 ≤ (tableEnvelope C).w2 12674 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12674 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12674 163 ∧ 0 ≤ d.f1 12674 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12674 163 ∧ 0 ≤ d.w1 12674 163 ∧ 0 ≤ d.w2 12674 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12674 ≤ 2 * (228 / 100 : ℝ) / 12674 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12674 ≤ 2 * (370 / 100 : ℝ) / 12674 := by
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
    (completeRAData (tableEnvelope C) 12674 163).locationBound 12674 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12674 163).energyBound 12674 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12674 163) (d.f1 12674 163) d.f2 ≤
      32 * (((4606242823 / 1000000000000000000) : ℝ) + (768360303 / 500000000000000000) + (184675683 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12674 163) (d.w1 12674 163)
      (d.w2 12674 163) ≤
      32 * (((922252577 / 50000000000000000000) : ℝ) + (656165091 / 50000000000000000000) + (239746247 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12674 163) (d.f1 12674 163) d.f2 ≤
      ((4606242823 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4606242823 / 1000000000000000000)) * ((768360303 / 500000000000000000)) * (126 / 100) +
      2 * (((768360303 / 500000000000000000)) ^ 2 + 2 * ((4606242823 / 1000000000000000000)) * ((184675683 / 500000000000000000))) +
      6 * ((768360303 / 500000000000000000)) * ((184675683 / 500000000000000000)) * (126 / 100) + 8 * ((184675683 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12674 163) (d.f1 12674 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12674 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12674 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12674 163) (d.f1 12674 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12674 163) (d.w1 12674 163) (d.w2 12674 163)
  have hwexpr0 : 0 ≤ d.w0 12674 163 + d.w1 12674 163 * √(π / 2) +
      2 * d.w2 12674 163 + energyR16 12674 *
      radiusPolynomialRoot16 (d.w0 12674 163) (d.w1 12674 163) (d.w2 12674 163) := by
    positivity
  constructor
  · change (12674 : ℝ) ^ 8 * (mA 12674 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12674 163) (d.f1 12674 163) d.f2 + locationR16 12674 *
        radiusPolynomialRoot16 (d.f0 12674 163) (d.f1 12674 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12674 : ℝ) ^ 8 * (mA 12674 : ℝ) ^ 8 *
        ((((4606242823 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4606242823 / 1000000000000000000)) * ((768360303 / 500000000000000000)) * (126 / 100) +
          2 * (((768360303 / 500000000000000000)) ^ 2 + 2 * ((4606242823 / 1000000000000000000)) * ((184675683 / 500000000000000000))) +
          6 * ((768360303 / 500000000000000000)) * ((184675683 / 500000000000000000)) * (126 / 100) + 8 * ((184675683 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12674) *
          (32 * (((4606242823 / 1000000000000000000) : ℝ) + (768360303 / 500000000000000000) + (184675683 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12674 : ℝ) ^ 16 *
      (d.w0 12674 163 + d.w1 12674 163 * √(π / 2) + 2 * d.w2 12674 163 +
        energyR16 12674 * radiusPolynomialRoot16 (d.w0 12674 163) (d.w1 12674 163)
          (d.w2 12674 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12674 : ℝ) ^ 16 *
        (((922252577 / 50000000000000000000) : ℝ) + ((656165091 / 50000000000000000000)) * (126 / 100) + 2 * ((239746247 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12674) *
          (32 * (((922252577 / 50000000000000000000) : ℝ) + (656165091 / 50000000000000000000) + (239746247 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12674
