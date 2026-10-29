import BstLean.Part266Shard32Step4


/-! A coarse bound on the actual paper statistics constant at dimension 13150. -/
namespace BstLean.Part266.Row13150
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13148 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13148 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13148 128 ≤ (13402 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13402 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13150) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13150 : ℕ))
    (by norm_num : (13150 : ℕ) ≤ 16384)
  have ht : paperTail256 13150 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13150 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13150 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13150 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13150 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13150 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13148 128 * √(2 / (13150 : ℝ)) *
      (√(13150 : ℝ) + paperT0 13150 + paperTail256 13150) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13150 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13150 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13150 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13148 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13148 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13150 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13150

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13150
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13150 (61 / 100) 166 (17 / (100 * 13150)) (26 / (10 * 13150)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13150 (61 / 100) 166 (17 / (100 * 13150)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (85855597 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (652894283 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3868221923 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13150 / 13150 * (61 / 100)) ^ 4 * inverseRadius8 (13150 - 1) /
            envelopeGap 13150 (61 / 100) 166 (17 / (100 * 13150)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13150

namespace BstLean.Part266.Row13150
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13150 166 ≤ (4200629641 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13150 166 ≤ (1401400937 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (42103401 / 125000000000000000)
  w0 : (tableEnvelope C).w0 13150 166 ≤ (412839549 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 13150 166 ≤ (146863717 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 13150 166 ≤ (429281733 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (85855597 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (85855597 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (652894283 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3868221923 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1797759 / 500000000) : ℝ) ≤ √(17 / (100 * 13150) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13150) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (258987809 / 125000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18067848281 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13150) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13150) ≤ (53772379 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13150) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13150 * (166 : ℝ) ^ 2 + 26 / (10 * 13150) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13150) : ℝ)) (tA 13150 * 166 ^ 2 + 26 / (10 * 13150)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1797759 / 500000000))) * ((85855597 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1797759 / 500000000)) ^ 3) * ((652894283 / 500000000000000000000000))) + ((3868221923 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1797759 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13150) : ℝ)) d.D d.V d.P (√(tA 13150) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1797759 / 500000000)) ^ 2 * (((258987809 / 125000000000000)) * ((18067848281 / 500000000000000000)))) + ((3868221923 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13150) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1797759 / 500000000)) * ((85855597 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13150) : ℝ)) (tA 13150 * 166 ^ 2 + 26 / (10 * 13150)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((85855597 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1797759 / 500000000)) ^ 2) * ((652894283 / 500000000000000000000000)) + ((3868221923 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13150) : ℝ)) (√(26 / (10 * 13150) : ℝ)) d.D d.V d.P (√(tA 13150) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1797759 / 500000000)) * (((258987809 / 125000000000000)) * ((18067848281 / 500000000000000000))) + ((3868221923 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13150) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((85855597 / 20000000000000000000) : ℝ) + ((3868221923 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13150

namespace BstLean.Part266.Row13150
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13150 166 ∧
    0 ≤ (tableEnvelope C).f1 13150 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13150 166 ∧
    0 ≤ (tableEnvelope C).w1 13150 166 ∧ 0 ≤ (tableEnvelope C).w2 13150 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13150 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13150 166 ∧ 0 ≤ d.f1 13150 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13150 166 ∧ 0 ≤ d.w1 13150 166 ∧ 0 ≤ d.w2 13150 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13150 ≤ 2 * (228 / 100 : ℝ) / 13150 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13150 ≤ 2 * (370 / 100 : ℝ) / 13150 := by
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
    (completeRAData (tableEnvelope C) 13150 166).locationBound 13150 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13150 166).energyBound 13150 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13150 166) (d.f1 13150 166) d.f2 ≤
      32 * (((4200629641 / 1000000000000000000) : ℝ) + (1401400937 / 1000000000000000000) + (42103401 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13150 166) (d.w1 13150 166)
      (d.w2 13150 166) ≤
      32 * (((412839549 / 25000000000000000000) : ℝ) + (146863717 / 12500000000000000000) + (429281733 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13150 166) (d.f1 13150 166) d.f2 ≤
      ((4200629641 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4200629641 / 1000000000000000000)) * ((1401400937 / 1000000000000000000)) * (126 / 100) +
      2 * (((1401400937 / 1000000000000000000)) ^ 2 + 2 * ((4200629641 / 1000000000000000000)) * ((42103401 / 125000000000000000))) +
      6 * ((1401400937 / 1000000000000000000)) * ((42103401 / 125000000000000000)) * (126 / 100) + 8 * ((42103401 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13150 166) (d.f1 13150 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13150 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13150 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13150 166) (d.f1 13150 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13150 166) (d.w1 13150 166) (d.w2 13150 166)
  have hwexpr0 : 0 ≤ d.w0 13150 166 + d.w1 13150 166 * √(π / 2) +
      2 * d.w2 13150 166 + energyR16 13150 *
      radiusPolynomialRoot16 (d.w0 13150 166) (d.w1 13150 166) (d.w2 13150 166) := by
    positivity
  constructor
  · change (13150 : ℝ) ^ 8 * (mA 13150 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13150 166) (d.f1 13150 166) d.f2 + locationR16 13150 *
        radiusPolynomialRoot16 (d.f0 13150 166) (d.f1 13150 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13150 : ℝ) ^ 8 * (mA 13150 : ℝ) ^ 8 *
        ((((4200629641 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4200629641 / 1000000000000000000)) * ((1401400937 / 1000000000000000000)) * (126 / 100) +
          2 * (((1401400937 / 1000000000000000000)) ^ 2 + 2 * ((4200629641 / 1000000000000000000)) * ((42103401 / 125000000000000000))) +
          6 * ((1401400937 / 1000000000000000000)) * ((42103401 / 125000000000000000)) * (126 / 100) + 8 * ((42103401 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13150) *
          (32 * (((4200629641 / 1000000000000000000) : ℝ) + (1401400937 / 1000000000000000000) + (42103401 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13150 : ℝ) ^ 16 *
      (d.w0 13150 166 + d.w1 13150 166 * √(π / 2) + 2 * d.w2 13150 166 +
        energyR16 13150 * radiusPolynomialRoot16 (d.w0 13150 166) (d.w1 13150 166)
          (d.w2 13150 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13150 : ℝ) ^ 16 *
        (((412839549 / 25000000000000000000) : ℝ) + ((146863717 / 12500000000000000000)) * (126 / 100) + 2 * ((429281733 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13150) *
          (32 * (((412839549 / 25000000000000000000) : ℝ) + (146863717 / 12500000000000000000) + (429281733 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13150

/-! A coarse bound on the actual paper statistics constant at dimension 13151. -/
namespace BstLean.Part266.Row13151
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13149 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13149 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13149 128 ≤ (13403 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13403 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13151) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13151 : ℕ))
    (by norm_num : (13151 : ℕ) ≤ 16384)
  have ht : paperTail256 13151 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13151 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13151 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13151 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13151 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13151 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13149 128 * √(2 / (13151 : ℝ)) *
      (√(13151 : ℝ) + paperT0 13151 + paperTail256 13151) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13151 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13151 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13151 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13149 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13149 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13151 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13151

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13151
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13151 (61 / 100) 166 (17 / (100 * 13151)) (26 / (10 * 13151)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13151 (61 / 100) 166 (17 / (100 * 13151)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (429180061 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (326347857 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1932923641 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13151 / 13151 * (61 / 100)) ^ 4 * inverseRadius8 (13151 - 1) /
            envelopeGap 13151 (61 / 100) 166 (17 / (100 * 13151)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13151

namespace BstLean.Part266.Row13151
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13151 166 ≤ (167993149 / 40000000000000000)
  f1 : (tableEnvelope C).f1 13151 166 ≤ (1401133981 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (336763111 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13151 166 ≤ (82549051 / 5000000000000000000)
  w1 : (tableEnvelope C).w1 13151 166 ≤ (1174641493 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13151 166 ≤ (214591903 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (429180061 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (429180061 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (326347857 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1932923641 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1797691 / 500000000) : ℝ) ≤ √(17 / (100 * 13151) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13151) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (64739567 / 31250000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9032550263 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13151) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13151) ≤ (5376829 / 50000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13151) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13151 * (166 : ℝ) ^ 2 + 26 / (10 * 13151) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13151) : ℝ)) (tA 13151 * 166 ^ 2 + 26 / (10 * 13151)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1797691 / 500000000))) * ((429180061 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1797691 / 500000000)) ^ 3) * ((326347857 / 250000000000000000000000))) + ((1932923641 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1797691 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13151) : ℝ)) d.D d.V d.P (√(tA 13151) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1797691 / 500000000)) ^ 2 * (((64739567 / 31250000000000)) * ((9032550263 / 250000000000000000)))) + ((1932923641 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13151) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1797691 / 500000000)) * ((429180061 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13151) : ℝ)) (tA 13151 * 166 ^ 2 + 26 / (10 * 13151)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((429180061 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1797691 / 500000000)) ^ 2) * ((326347857 / 250000000000000000000000)) + ((1932923641 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13151) : ℝ)) (√(26 / (10 * 13151) : ℝ)) d.D d.V d.P (√(tA 13151) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1797691 / 500000000)) * (((64739567 / 31250000000000)) * ((9032550263 / 250000000000000000))) + ((1932923641 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13151) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((429180061 / 100000000000000000000) : ℝ) + ((1932923641 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13151

namespace BstLean.Part266.Row13151
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13151 166 ∧
    0 ≤ (tableEnvelope C).f1 13151 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13151 166 ∧
    0 ≤ (tableEnvelope C).w1 13151 166 ∧ 0 ≤ (tableEnvelope C).w2 13151 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13151 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13151 166 ∧ 0 ≤ d.f1 13151 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13151 166 ∧ 0 ≤ d.w1 13151 166 ∧ 0 ≤ d.w2 13151 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13151 ≤ 2 * (228 / 100 : ℝ) / 13151 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13151 ≤ 2 * (370 / 100 : ℝ) / 13151 := by
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
    (completeRAData (tableEnvelope C) 13151 166).locationBound 13151 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13151 166).energyBound 13151 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13151 166) (d.f1 13151 166) d.f2 ≤
      32 * (((167993149 / 40000000000000000) : ℝ) + (1401133981 / 1000000000000000000) + (336763111 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13151 166) (d.w1 13151 166)
      (d.w2 13151 166) ≤
      32 * (((82549051 / 5000000000000000000) : ℝ) + (1174641493 / 100000000000000000000) + (214591903 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13151 166) (d.f1 13151 166) d.f2 ≤
      ((167993149 / 40000000000000000) : ℝ) ^ 2 + 2 * ((167993149 / 40000000000000000)) * ((1401133981 / 1000000000000000000)) * (126 / 100) +
      2 * (((1401133981 / 1000000000000000000)) ^ 2 + 2 * ((167993149 / 40000000000000000)) * ((336763111 / 1000000000000000000))) +
      6 * ((1401133981 / 1000000000000000000)) * ((336763111 / 1000000000000000000)) * (126 / 100) + 8 * ((336763111 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13151 166) (d.f1 13151 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13151 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13151 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13151 166) (d.f1 13151 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13151 166) (d.w1 13151 166) (d.w2 13151 166)
  have hwexpr0 : 0 ≤ d.w0 13151 166 + d.w1 13151 166 * √(π / 2) +
      2 * d.w2 13151 166 + energyR16 13151 *
      radiusPolynomialRoot16 (d.w0 13151 166) (d.w1 13151 166) (d.w2 13151 166) := by
    positivity
  constructor
  · change (13151 : ℝ) ^ 8 * (mA 13151 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13151 166) (d.f1 13151 166) d.f2 + locationR16 13151 *
        radiusPolynomialRoot16 (d.f0 13151 166) (d.f1 13151 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13151 : ℝ) ^ 8 * (mA 13151 : ℝ) ^ 8 *
        ((((167993149 / 40000000000000000) : ℝ) ^ 2 + 2 * ((167993149 / 40000000000000000)) * ((1401133981 / 1000000000000000000)) * (126 / 100) +
          2 * (((1401133981 / 1000000000000000000)) ^ 2 + 2 * ((167993149 / 40000000000000000)) * ((336763111 / 1000000000000000000))) +
          6 * ((1401133981 / 1000000000000000000)) * ((336763111 / 1000000000000000000)) * (126 / 100) + 8 * ((336763111 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13151) *
          (32 * (((167993149 / 40000000000000000) : ℝ) + (1401133981 / 1000000000000000000) + (336763111 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13151 : ℝ) ^ 16 *
      (d.w0 13151 166 + d.w1 13151 166 * √(π / 2) + 2 * d.w2 13151 166 +
        energyR16 13151 * radiusPolynomialRoot16 (d.w0 13151 166) (d.w1 13151 166)
          (d.w2 13151 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13151 : ℝ) ^ 16 *
        (((82549051 / 5000000000000000000) : ℝ) + ((1174641493 / 100000000000000000000)) * (126 / 100) + 2 * ((214591903 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13151) *
          (32 * (((82549051 / 5000000000000000000) : ℝ) + (1174641493 / 100000000000000000000) + (214591903 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13151

/-! A coarse bound on the actual paper statistics constant at dimension 13152. -/
namespace BstLean.Part266.Row13152
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13150 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13150 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13150 128 ≤ (13404 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13404 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13152) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13152 : ℕ))
    (by norm_num : (13152 : ℕ) ≤ 16384)
  have ht : paperTail256 13152 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13152 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13152 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13152 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13152 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13152 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13150 128 * √(2 / (13152 : ℝ)) *
      (√(13152 : ℝ) + paperT0 13152 + paperTail256 13152) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13152 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13152 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13152 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13150 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13150 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13152 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13152

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13152
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13152 (61 / 100) 166 (17 / (100 * 13152)) (26 / (10 * 13152)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13152 (61 / 100) 166 (17 / (100 * 13152)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (429082167 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (652497221 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3863474283 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13152 / 13152 * (61 / 100)) ^ 4 * inverseRadius8 (13152 - 1) /
            envelopeGap 13152 (61 / 100) 166 (17 / (100 * 13152)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13152

namespace BstLean.Part266.Row13152
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13152 166 ≤ (4199031449 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13152 166 ≤ (1400867889 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (336699127 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13152 166 ≤ (1650604649 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13152 166 ≤ (36699177 / 3125000000000000000)
  w2 : (tableEnvelope C).w2 13152 166 ≤ (42908591 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (429082167 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (429082167 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (652497221 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3863474283 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((719049 / 200000000) : ℝ) ≤ √(17 / (100 * 13152) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13152) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1035714931 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36124706809 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13152) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13152) ≤ (26882101 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13152) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13152 * (166 : ℝ) ^ 2 + 26 / (10 * 13152) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13152) : ℝ)) (tA 13152 * 166 ^ 2 + 26 / (10 * 13152)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((719049 / 200000000))) * ((429082167 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((719049 / 200000000)) ^ 3) * ((652497221 / 500000000000000000000000))) + ((3863474283 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((719049 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13152) : ℝ)) d.D d.V d.P (√(tA 13152) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((719049 / 200000000)) ^ 2 * (((1035714931 / 500000000000000)) * ((36124706809 / 1000000000000000000)))) + ((3863474283 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13152) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((719049 / 200000000)) * ((429082167 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13152) : ℝ)) (tA 13152 * 166 ^ 2 + 26 / (10 * 13152)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((429082167 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((719049 / 200000000)) ^ 2) * ((652497221 / 500000000000000000000000)) + ((3863474283 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13152) : ℝ)) (√(26 / (10 * 13152) : ℝ)) d.D d.V d.P (√(tA 13152) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((719049 / 200000000)) * (((1035714931 / 500000000000000)) * ((36124706809 / 1000000000000000000))) + ((3863474283 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13152) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((429082167 / 100000000000000000000) : ℝ) + ((3863474283 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13152

namespace BstLean.Part266.Row13152
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13152 166 ∧
    0 ≤ (tableEnvelope C).f1 13152 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13152 166 ∧
    0 ≤ (tableEnvelope C).w1 13152 166 ∧ 0 ≤ (tableEnvelope C).w2 13152 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13152 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13152 166 ∧ 0 ≤ d.f1 13152 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13152 166 ∧ 0 ≤ d.w1 13152 166 ∧ 0 ≤ d.w2 13152 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13152 ≤ 2 * (228 / 100 : ℝ) / 13152 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13152 ≤ 2 * (370 / 100 : ℝ) / 13152 := by
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
    (completeRAData (tableEnvelope C) 13152 166).locationBound 13152 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13152 166).energyBound 13152 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13152 166) (d.f1 13152 166) d.f2 ≤
      32 * (((4199031449 / 1000000000000000000) : ℝ) + (1400867889 / 1000000000000000000) + (336699127 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13152 166) (d.w1 13152 166)
      (d.w2 13152 166) ≤
      32 * (((1650604649 / 100000000000000000000) : ℝ) + (36699177 / 3125000000000000000) + (42908591 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13152 166) (d.f1 13152 166) d.f2 ≤
      ((4199031449 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4199031449 / 1000000000000000000)) * ((1400867889 / 1000000000000000000)) * (126 / 100) +
      2 * (((1400867889 / 1000000000000000000)) ^ 2 + 2 * ((4199031449 / 1000000000000000000)) * ((336699127 / 1000000000000000000))) +
      6 * ((1400867889 / 1000000000000000000)) * ((336699127 / 1000000000000000000)) * (126 / 100) + 8 * ((336699127 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13152 166) (d.f1 13152 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13152 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13152 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13152 166) (d.f1 13152 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13152 166) (d.w1 13152 166) (d.w2 13152 166)
  have hwexpr0 : 0 ≤ d.w0 13152 166 + d.w1 13152 166 * √(π / 2) +
      2 * d.w2 13152 166 + energyR16 13152 *
      radiusPolynomialRoot16 (d.w0 13152 166) (d.w1 13152 166) (d.w2 13152 166) := by
    positivity
  constructor
  · change (13152 : ℝ) ^ 8 * (mA 13152 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13152 166) (d.f1 13152 166) d.f2 + locationR16 13152 *
        radiusPolynomialRoot16 (d.f0 13152 166) (d.f1 13152 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13152 : ℝ) ^ 8 * (mA 13152 : ℝ) ^ 8 *
        ((((4199031449 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4199031449 / 1000000000000000000)) * ((1400867889 / 1000000000000000000)) * (126 / 100) +
          2 * (((1400867889 / 1000000000000000000)) ^ 2 + 2 * ((4199031449 / 1000000000000000000)) * ((336699127 / 1000000000000000000))) +
          6 * ((1400867889 / 1000000000000000000)) * ((336699127 / 1000000000000000000)) * (126 / 100) + 8 * ((336699127 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13152) *
          (32 * (((4199031449 / 1000000000000000000) : ℝ) + (1400867889 / 1000000000000000000) + (336699127 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13152 : ℝ) ^ 16 *
      (d.w0 13152 166 + d.w1 13152 166 * √(π / 2) + 2 * d.w2 13152 166 +
        energyR16 13152 * radiusPolynomialRoot16 (d.w0 13152 166) (d.w1 13152 166)
          (d.w2 13152 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13152 : ℝ) ^ 16 *
        (((1650604649 / 100000000000000000000) : ℝ) + ((36699177 / 3125000000000000000)) * (126 / 100) + 2 * ((42908591 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13152) *
          (32 * (((1650604649 / 100000000000000000000) : ℝ) + (36699177 / 3125000000000000000) + (42908591 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13152

/-! A coarse bound on the actual paper statistics constant at dimension 13153. -/
namespace BstLean.Part266.Row13153
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13151 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13151 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13151 128 ≤ (13405 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13405 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13153) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13153 : ℕ))
    (by norm_num : (13153 : ℕ) ≤ 16384)
  have ht : paperTail256 13153 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13153 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13153 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13153 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13153 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13153 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13151 128 * √(2 / (13153 : ℝ)) *
      (√(13153 : ℝ) + paperT0 13153 + paperTail256 13153) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13153 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13153 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13153 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13151 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13151 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13153 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13153

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13153
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13153 (61 / 100) 166 (17 / (100 * 13153)) (26 / (10 * 13153)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13153 (61 / 100) 166 (17 / (100 * 13153)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (214492151 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (652298803 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (965275731 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13153 / 13153 * (61 / 100)) ^ 4 * inverseRadius8 (13153 - 1) /
            envelopeGap 13153 (61 / 100) 166 (17 / (100 * 13153)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13153

namespace BstLean.Part266.Row13153
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13153 166 ≤ (1049558609 / 250000000000000000)
  f1 : (tableEnvelope C).f1 13153 166 ≤ (700300939 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (8415879 / 25000000000000000)
  w0 : (tableEnvelope C).w0 13153 166 ≤ (825114201 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13153 166 ≤ (3669081 / 312500000000000000)
  w2 : (tableEnvelope C).w2 13153 166 ≤ (428988043 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (214492151 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (214492151 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (652298803 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (965275731 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((898777 / 250000000) : ℝ) ≤ √(17 / (100 * 13153) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13153) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2071193623 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36119213807 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13153) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13153) ≤ (107520229 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13153) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13153 * (166 : ℝ) ^ 2 + 26 / (10 * 13153) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13153) : ℝ)) (tA 13153 * 166 ^ 2 + 26 / (10 * 13153)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((898777 / 250000000))) * ((214492151 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((898777 / 250000000)) ^ 3) * ((652298803 / 500000000000000000000000))) + ((965275731 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((898777 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13153) : ℝ)) d.D d.V d.P (√(tA 13153) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((898777 / 250000000)) ^ 2 * (((2071193623 / 1000000000000000)) * ((36119213807 / 1000000000000000000)))) + ((965275731 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13153) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((898777 / 250000000)) * ((214492151 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13153) : ℝ)) (tA 13153 * 166 ^ 2 + 26 / (10 * 13153)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((214492151 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((898777 / 250000000)) ^ 2) * ((652298803 / 500000000000000000000000)) + ((965275731 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13153) : ℝ)) (√(26 / (10 * 13153) : ℝ)) d.D d.V d.P (√(tA 13153) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((898777 / 250000000)) * (((2071193623 / 1000000000000000)) * ((36119213807 / 1000000000000000000))) + ((965275731 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13153) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((214492151 / 50000000000000000000) : ℝ) + ((965275731 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13153

namespace BstLean.Part266.Row13153
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13153 166 ∧
    0 ≤ (tableEnvelope C).f1 13153 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13153 166 ∧
    0 ≤ (tableEnvelope C).w1 13153 166 ∧ 0 ≤ (tableEnvelope C).w2 13153 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13153 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13153 166 ∧ 0 ≤ d.f1 13153 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13153 166 ∧ 0 ≤ d.w1 13153 166 ∧ 0 ≤ d.w2 13153 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13153 ≤ 2 * (228 / 100 : ℝ) / 13153 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13153 ≤ 2 * (370 / 100 : ℝ) / 13153 := by
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
    (completeRAData (tableEnvelope C) 13153 166).locationBound 13153 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13153 166).energyBound 13153 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13153 166) (d.f1 13153 166) d.f2 ≤
      32 * (((1049558609 / 250000000000000000) : ℝ) + (700300939 / 500000000000000000) + (8415879 / 25000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13153 166) (d.w1 13153 166)
      (d.w2 13153 166) ≤
      32 * (((825114201 / 50000000000000000000) : ℝ) + (3669081 / 312500000000000000) + (428988043 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13153 166) (d.f1 13153 166) d.f2 ≤
      ((1049558609 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1049558609 / 250000000000000000)) * ((700300939 / 500000000000000000)) * (126 / 100) +
      2 * (((700300939 / 500000000000000000)) ^ 2 + 2 * ((1049558609 / 250000000000000000)) * ((8415879 / 25000000000000000))) +
      6 * ((700300939 / 500000000000000000)) * ((8415879 / 25000000000000000)) * (126 / 100) + 8 * ((8415879 / 25000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13153 166) (d.f1 13153 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13153 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13153 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13153 166) (d.f1 13153 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13153 166) (d.w1 13153 166) (d.w2 13153 166)
  have hwexpr0 : 0 ≤ d.w0 13153 166 + d.w1 13153 166 * √(π / 2) +
      2 * d.w2 13153 166 + energyR16 13153 *
      radiusPolynomialRoot16 (d.w0 13153 166) (d.w1 13153 166) (d.w2 13153 166) := by
    positivity
  constructor
  · change (13153 : ℝ) ^ 8 * (mA 13153 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13153 166) (d.f1 13153 166) d.f2 + locationR16 13153 *
        radiusPolynomialRoot16 (d.f0 13153 166) (d.f1 13153 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13153 : ℝ) ^ 8 * (mA 13153 : ℝ) ^ 8 *
        ((((1049558609 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1049558609 / 250000000000000000)) * ((700300939 / 500000000000000000)) * (126 / 100) +
          2 * (((700300939 / 500000000000000000)) ^ 2 + 2 * ((1049558609 / 250000000000000000)) * ((8415879 / 25000000000000000))) +
          6 * ((700300939 / 500000000000000000)) * ((8415879 / 25000000000000000)) * (126 / 100) + 8 * ((8415879 / 25000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13153) *
          (32 * (((1049558609 / 250000000000000000) : ℝ) + (700300939 / 500000000000000000) + (8415879 / 25000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13153 : ℝ) ^ 16 *
      (d.w0 13153 166 + d.w1 13153 166 * √(π / 2) + 2 * d.w2 13153 166 +
        energyR16 13153 * radiusPolynomialRoot16 (d.w0 13153 166) (d.w1 13153 166)
          (d.w2 13153 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13153 : ℝ) ^ 16 *
        (((825114201 / 50000000000000000000) : ℝ) + ((3669081 / 312500000000000000)) * (126 / 100) + 2 * ((428988043 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13153) *
          (32 * (((825114201 / 50000000000000000000) : ℝ) + (3669081 / 312500000000000000) + (428988043 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13153

/-! A coarse bound on the actual paper statistics constant at dimension 13154. -/
namespace BstLean.Part266.Row13154
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13152 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13152 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13152 128 ≤ (13406 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13406 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13154) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13154 : ℕ))
    (by norm_num : (13154 : ℕ) ≤ 16384)
  have ht : paperTail256 13154 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13154 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13154 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13154 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13154 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13154 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13152 128 * √(2 / (13154 : ℝ)) *
      (√(13154 : ℝ) + paperT0 13154 + paperTail256 13154) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13154 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13154 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13154 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13152 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13152 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13154 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13154

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13154
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13154 (61 / 100) 166 (17 / (100 * 13154)) (26 / (10 * 13154)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13154 (61 / 100) 166 (17 / (100 * 13154)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (428886467 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1304200921 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (964683301 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13154 / 13154 * (61 / 100)) ^ 4 * inverseRadius8 (13154 - 1) /
            envelopeGap 13154 (61 / 100) 166 (17 / (100 * 13154)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13154

namespace BstLean.Part266.Row13154
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13154 166 ≤ (4197434317 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13154 166 ≤ (350083793 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (336571119 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13154 166 ≤ (824925801 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13154 166 ≤ (73364871 / 6250000000000000000)
  w2 : (tableEnvelope C).w2 13154 166 ≤ (85778041 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (428886467 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (428886467 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1304200921 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (964683301 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((898743 / 250000000) : ℝ) ≤ √(17 / (100 * 13154) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13154) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2070957429 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1805686103 / 50000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13154) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13154) ≤ (21502411 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13154) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13154 * (166 : ℝ) ^ 2 + 26 / (10 * 13154) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13154) : ℝ)) (tA 13154 * 166 ^ 2 + 26 / (10 * 13154)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((898743 / 250000000))) * ((428886467 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((898743 / 250000000)) ^ 3) * ((1304200921 / 1000000000000000000000000))) + ((964683301 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((898743 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13154) : ℝ)) d.D d.V d.P (√(tA 13154) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((898743 / 250000000)) ^ 2 * (((2070957429 / 1000000000000000)) * ((1805686103 / 50000000000000000)))) + ((964683301 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13154) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((898743 / 250000000)) * ((428886467 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13154) : ℝ)) (tA 13154 * 166 ^ 2 + 26 / (10 * 13154)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((428886467 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((898743 / 250000000)) ^ 2) * ((1304200921 / 1000000000000000000000000)) + ((964683301 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13154) : ℝ)) (√(26 / (10 * 13154) : ℝ)) d.D d.V d.P (√(tA 13154) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((898743 / 250000000)) * (((2070957429 / 1000000000000000)) * ((1805686103 / 50000000000000000))) + ((964683301 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13154) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((428886467 / 100000000000000000000) : ℝ) + ((964683301 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13154

namespace BstLean.Part266.Row13154
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13154 166 ∧
    0 ≤ (tableEnvelope C).f1 13154 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13154 166 ∧
    0 ≤ (tableEnvelope C).w1 13154 166 ∧ 0 ≤ (tableEnvelope C).w2 13154 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13154 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13154 166 ∧ 0 ≤ d.f1 13154 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13154 166 ∧ 0 ≤ d.w1 13154 166 ∧ 0 ≤ d.w2 13154 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13154 ≤ 2 * (228 / 100 : ℝ) / 13154 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13154 ≤ 2 * (370 / 100 : ℝ) / 13154 := by
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
    (completeRAData (tableEnvelope C) 13154 166).locationBound 13154 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13154 166).energyBound 13154 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13154 166) (d.f1 13154 166) d.f2 ≤
      32 * (((4197434317 / 1000000000000000000) : ℝ) + (350083793 / 250000000000000000) + (336571119 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13154 166) (d.w1 13154 166)
      (d.w2 13154 166) ≤
      32 * (((824925801 / 50000000000000000000) : ℝ) + (73364871 / 6250000000000000000) + (85778041 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13154 166) (d.f1 13154 166) d.f2 ≤
      ((4197434317 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4197434317 / 1000000000000000000)) * ((350083793 / 250000000000000000)) * (126 / 100) +
      2 * (((350083793 / 250000000000000000)) ^ 2 + 2 * ((4197434317 / 1000000000000000000)) * ((336571119 / 1000000000000000000))) +
      6 * ((350083793 / 250000000000000000)) * ((336571119 / 1000000000000000000)) * (126 / 100) + 8 * ((336571119 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13154 166) (d.f1 13154 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13154 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13154 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13154 166) (d.f1 13154 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13154 166) (d.w1 13154 166) (d.w2 13154 166)
  have hwexpr0 : 0 ≤ d.w0 13154 166 + d.w1 13154 166 * √(π / 2) +
      2 * d.w2 13154 166 + energyR16 13154 *
      radiusPolynomialRoot16 (d.w0 13154 166) (d.w1 13154 166) (d.w2 13154 166) := by
    positivity
  constructor
  · change (13154 : ℝ) ^ 8 * (mA 13154 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13154 166) (d.f1 13154 166) d.f2 + locationR16 13154 *
        radiusPolynomialRoot16 (d.f0 13154 166) (d.f1 13154 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13154 : ℝ) ^ 8 * (mA 13154 : ℝ) ^ 8 *
        ((((4197434317 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4197434317 / 1000000000000000000)) * ((350083793 / 250000000000000000)) * (126 / 100) +
          2 * (((350083793 / 250000000000000000)) ^ 2 + 2 * ((4197434317 / 1000000000000000000)) * ((336571119 / 1000000000000000000))) +
          6 * ((350083793 / 250000000000000000)) * ((336571119 / 1000000000000000000)) * (126 / 100) + 8 * ((336571119 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13154) *
          (32 * (((4197434317 / 1000000000000000000) : ℝ) + (350083793 / 250000000000000000) + (336571119 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13154 : ℝ) ^ 16 *
      (d.w0 13154 166 + d.w1 13154 166 * √(π / 2) + 2 * d.w2 13154 166 +
        energyR16 13154 * radiusPolynomialRoot16 (d.w0 13154 166) (d.w1 13154 166)
          (d.w2 13154 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13154 : ℝ) ^ 16 *
        (((824925801 / 50000000000000000000) : ℝ) + ((73364871 / 6250000000000000000)) * (126 / 100) + 2 * ((85778041 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13154) *
          (32 * (((824925801 / 50000000000000000000) : ℝ) + (73364871 / 6250000000000000000) + (85778041 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13154

/-! A coarse bound on the actual paper statistics constant at dimension 13155. -/
namespace BstLean.Part266.Row13155
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13153 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13153 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13153 128 ≤ (13407 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13407 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13155) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13155 : ℕ))
    (by norm_num : (13155 : ℕ) ≤ 16384)
  have ht : paperTail256 13155 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13155 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13155 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13155 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13155 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13155 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13153 128 * √(2 / (13155 : ℝ)) *
      (√(13155 : ℝ) + paperT0 13155 + paperTail256 13155) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13155 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13155 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13155 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13153 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13153 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13155 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13155

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13155
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13155 (61 / 100) 166 (17 / (100 * 13155)) (26 / (10 * 13155)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13155 (61 / 100) 166 (17 / (100 * 13155)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (214394331 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1303804387 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1928182561 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13155 / 13155 * (61 / 100)) ^ 4 * inverseRadius8 (13155 - 1) /
            envelopeGap 13155 (61 / 100) 166 (17 / (100 * 13155)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13155

namespace BstLean.Part266.Row13155
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13155 166 ≤ (2098318917 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13155 166 ≤ (87504333 / 62500000000000000)
  f2 : (tableEnvelope C).f2 ≤ (33650719 / 100000000000000000)
  w0 : (tableEnvelope C).w0 13155 166 ≤ (824737803 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13155 166 ≤ (586785183 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13155 166 ≤ (214396199 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (214394331 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (214394331 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1303804387 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1928182561 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((718967 / 200000000) : ℝ) ≤ √(17 / (100 * 13155) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13155) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2070721281 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36108231569 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13155) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13155) ≤ (53751941 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13155) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13155 * (166 : ℝ) ^ 2 + 26 / (10 * 13155) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13155) : ℝ)) (tA 13155 * 166 ^ 2 + 26 / (10 * 13155)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((718967 / 200000000))) * ((214394331 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((718967 / 200000000)) ^ 3) * ((1303804387 / 1000000000000000000000000))) + ((1928182561 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((718967 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13155) : ℝ)) d.D d.V d.P (√(tA 13155) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((718967 / 200000000)) ^ 2 * (((2070721281 / 1000000000000000)) * ((36108231569 / 1000000000000000000)))) + ((1928182561 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13155) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((718967 / 200000000)) * ((214394331 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13155) : ℝ)) (tA 13155 * 166 ^ 2 + 26 / (10 * 13155)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((214394331 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((718967 / 200000000)) ^ 2) * ((1303804387 / 1000000000000000000000000)) + ((1928182561 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13155) : ℝ)) (√(26 / (10 * 13155) : ℝ)) d.D d.V d.P (√(tA 13155) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((718967 / 200000000)) * (((2070721281 / 1000000000000000)) * ((36108231569 / 1000000000000000000))) + ((1928182561 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13155) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((214394331 / 50000000000000000000) : ℝ) + ((1928182561 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13155

namespace BstLean.Part266.Row13155
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13155 166 ∧
    0 ≤ (tableEnvelope C).f1 13155 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13155 166 ∧
    0 ≤ (tableEnvelope C).w1 13155 166 ∧ 0 ≤ (tableEnvelope C).w2 13155 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13155 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13155 166 ∧ 0 ≤ d.f1 13155 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13155 166 ∧ 0 ≤ d.w1 13155 166 ∧ 0 ≤ d.w2 13155 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13155 ≤ 2 * (228 / 100 : ℝ) / 13155 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13155 ≤ 2 * (370 / 100 : ℝ) / 13155 := by
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
    (completeRAData (tableEnvelope C) 13155 166).locationBound 13155 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13155 166).energyBound 13155 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13155 166) (d.f1 13155 166) d.f2 ≤
      32 * (((2098318917 / 500000000000000000) : ℝ) + (87504333 / 62500000000000000) + (33650719 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13155 166) (d.w1 13155 166)
      (d.w2 13155 166) ≤
      32 * (((824737803 / 50000000000000000000) : ℝ) + (586785183 / 50000000000000000000) + (214396199 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13155 166) (d.f1 13155 166) d.f2 ≤
      ((2098318917 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2098318917 / 500000000000000000)) * ((87504333 / 62500000000000000)) * (126 / 100) +
      2 * (((87504333 / 62500000000000000)) ^ 2 + 2 * ((2098318917 / 500000000000000000)) * ((33650719 / 100000000000000000))) +
      6 * ((87504333 / 62500000000000000)) * ((33650719 / 100000000000000000)) * (126 / 100) + 8 * ((33650719 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13155 166) (d.f1 13155 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13155 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13155 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13155 166) (d.f1 13155 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13155 166) (d.w1 13155 166) (d.w2 13155 166)
  have hwexpr0 : 0 ≤ d.w0 13155 166 + d.w1 13155 166 * √(π / 2) +
      2 * d.w2 13155 166 + energyR16 13155 *
      radiusPolynomialRoot16 (d.w0 13155 166) (d.w1 13155 166) (d.w2 13155 166) := by
    positivity
  constructor
  · change (13155 : ℝ) ^ 8 * (mA 13155 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13155 166) (d.f1 13155 166) d.f2 + locationR16 13155 *
        radiusPolynomialRoot16 (d.f0 13155 166) (d.f1 13155 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13155 : ℝ) ^ 8 * (mA 13155 : ℝ) ^ 8 *
        ((((2098318917 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2098318917 / 500000000000000000)) * ((87504333 / 62500000000000000)) * (126 / 100) +
          2 * (((87504333 / 62500000000000000)) ^ 2 + 2 * ((2098318917 / 500000000000000000)) * ((33650719 / 100000000000000000))) +
          6 * ((87504333 / 62500000000000000)) * ((33650719 / 100000000000000000)) * (126 / 100) + 8 * ((33650719 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13155) *
          (32 * (((2098318917 / 500000000000000000) : ℝ) + (87504333 / 62500000000000000) + (33650719 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13155 : ℝ) ^ 16 *
      (d.w0 13155 166 + d.w1 13155 166 * √(π / 2) + 2 * d.w2 13155 166 +
        energyR16 13155 * radiusPolynomialRoot16 (d.w0 13155 166) (d.w1 13155 166)
          (d.w2 13155 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13155 : ℝ) ^ 16 *
        (((824737803 / 50000000000000000000) : ℝ) + ((586785183 / 50000000000000000000)) * (126 / 100) + 2 * ((214396199 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13155) *
          (32 * (((824737803 / 50000000000000000000) : ℝ) + (586785183 / 50000000000000000000) + (214396199 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13155

/-! A coarse bound on the actual paper statistics constant at dimension 13156. -/
namespace BstLean.Part266.Row13156
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13154 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13154 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13154 128 ≤ (13408 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13408 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13156) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13156 : ℕ))
    (by norm_num : (13156 : ℕ) ≤ 16384)
  have ht : paperTail256 13156 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13156 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13156 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13156 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13156 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13156 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13154 128 * √(2 / (13156 : ℝ)) *
      (√(13156 : ℝ) + paperT0 13156 + paperTail256 13156) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13156 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13156 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13156 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13154 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13154 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13156 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13156

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13156
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13156 (61 / 100) 166 (17 / (100 * 13156)) (26 / (10 * 13156)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13156 (61 / 100) 166 (17 / (100 * 13156)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (428690887 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1303408003 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (963499669 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13156 / 13156 * (61 / 100)) ^ 4 * inverseRadius8 (13156 - 1) /
            envelopeGap 13156 (61 / 100) 166 (17 / (100 * 13156)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13156

namespace BstLean.Part266.Row13156
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13156 166 ≤ (2097920807 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13156 166 ≤ (1399803567 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (336443279 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13156 166 ≤ (824549867 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13156 166 ≤ (586651441 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13156 166 ≤ (428694621 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (428690887 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (428690887 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1303408003 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (963499669 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1797349 / 500000000) : ℝ) ≤ √(17 / (100 * 13156) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13156) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1035242589 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (451284279 / 12500000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13156) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13156) ≤ (107495711 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13156) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13156 * (166 : ℝ) ^ 2 + 26 / (10 * 13156) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13156) : ℝ)) (tA 13156 * 166 ^ 2 + 26 / (10 * 13156)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1797349 / 500000000))) * ((428690887 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1797349 / 500000000)) ^ 3) * ((1303408003 / 1000000000000000000000000))) + ((963499669 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1797349 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13156) : ℝ)) d.D d.V d.P (√(tA 13156) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1797349 / 500000000)) ^ 2 * (((1035242589 / 500000000000000)) * ((451284279 / 12500000000000000)))) + ((963499669 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13156) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1797349 / 500000000)) * ((428690887 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13156) : ℝ)) (tA 13156 * 166 ^ 2 + 26 / (10 * 13156)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((428690887 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1797349 / 500000000)) ^ 2) * ((1303408003 / 1000000000000000000000000)) + ((963499669 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13156) : ℝ)) (√(26 / (10 * 13156) : ℝ)) d.D d.V d.P (√(tA 13156) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1797349 / 500000000)) * (((1035242589 / 500000000000000)) * ((451284279 / 12500000000000000))) + ((963499669 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13156) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((428690887 / 100000000000000000000) : ℝ) + ((963499669 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13156

namespace BstLean.Part266.Row13156
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13156 166 ∧
    0 ≤ (tableEnvelope C).f1 13156 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13156 166 ∧
    0 ≤ (tableEnvelope C).w1 13156 166 ∧ 0 ≤ (tableEnvelope C).w2 13156 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13156 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13156 166 ∧ 0 ≤ d.f1 13156 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13156 166 ∧ 0 ≤ d.w1 13156 166 ∧ 0 ≤ d.w2 13156 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13156 ≤ 2 * (228 / 100 : ℝ) / 13156 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13156 ≤ 2 * (370 / 100 : ℝ) / 13156 := by
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
    (completeRAData (tableEnvelope C) 13156 166).locationBound 13156 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13156 166).energyBound 13156 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13156 166) (d.f1 13156 166) d.f2 ≤
      32 * (((2097920807 / 500000000000000000) : ℝ) + (1399803567 / 1000000000000000000) + (336443279 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13156 166) (d.w1 13156 166)
      (d.w2 13156 166) ≤
      32 * (((824549867 / 50000000000000000000) : ℝ) + (586651441 / 50000000000000000000) + (428694621 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13156 166) (d.f1 13156 166) d.f2 ≤
      ((2097920807 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2097920807 / 500000000000000000)) * ((1399803567 / 1000000000000000000)) * (126 / 100) +
      2 * (((1399803567 / 1000000000000000000)) ^ 2 + 2 * ((2097920807 / 500000000000000000)) * ((336443279 / 1000000000000000000))) +
      6 * ((1399803567 / 1000000000000000000)) * ((336443279 / 1000000000000000000)) * (126 / 100) + 8 * ((336443279 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13156 166) (d.f1 13156 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13156 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13156 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13156 166) (d.f1 13156 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13156 166) (d.w1 13156 166) (d.w2 13156 166)
  have hwexpr0 : 0 ≤ d.w0 13156 166 + d.w1 13156 166 * √(π / 2) +
      2 * d.w2 13156 166 + energyR16 13156 *
      radiusPolynomialRoot16 (d.w0 13156 166) (d.w1 13156 166) (d.w2 13156 166) := by
    positivity
  constructor
  · change (13156 : ℝ) ^ 8 * (mA 13156 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13156 166) (d.f1 13156 166) d.f2 + locationR16 13156 *
        radiusPolynomialRoot16 (d.f0 13156 166) (d.f1 13156 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13156 : ℝ) ^ 8 * (mA 13156 : ℝ) ^ 8 *
        ((((2097920807 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2097920807 / 500000000000000000)) * ((1399803567 / 1000000000000000000)) * (126 / 100) +
          2 * (((1399803567 / 1000000000000000000)) ^ 2 + 2 * ((2097920807 / 500000000000000000)) * ((336443279 / 1000000000000000000))) +
          6 * ((1399803567 / 1000000000000000000)) * ((336443279 / 1000000000000000000)) * (126 / 100) + 8 * ((336443279 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13156) *
          (32 * (((2097920807 / 500000000000000000) : ℝ) + (1399803567 / 1000000000000000000) + (336443279 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13156 : ℝ) ^ 16 *
      (d.w0 13156 166 + d.w1 13156 166 * √(π / 2) + 2 * d.w2 13156 166 +
        energyR16 13156 * radiusPolynomialRoot16 (d.w0 13156 166) (d.w1 13156 166)
          (d.w2 13156 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13156 : ℝ) ^ 16 *
        (((824549867 / 50000000000000000000) : ℝ) + ((586651441 / 50000000000000000000)) * (126 / 100) + 2 * ((428694621 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13156) *
          (32 * (((824549867 / 50000000000000000000) : ℝ) + (586651441 / 50000000000000000000) + (428694621 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13156

/-! A coarse bound on the actual paper statistics constant at dimension 13157. -/
namespace BstLean.Part266.Row13157
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13155 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13155 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13155 128 ≤ (13409 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13409 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13157) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13157 : ℕ))
    (by norm_num : (13157 : ℕ) ≤ 16384)
  have ht : paperTail256 13157 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13157 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13157 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13157 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13157 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13157 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13155 128 * √(2 / (13157 : ℝ)) *
      (√(13157 : ℝ) + paperT0 13157 + paperTail256 13157) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13157 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13157 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13157 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13155 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13155 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13157 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13157

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13157
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13157 (61 / 100) 166 (17 / (100 * 13157)) (26 / (10 * 13157)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13157 (61 / 100) 166 (17 / (100 * 13157)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (428593141 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (130301177 / 100000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (770326773 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13157 / 13157 * (61 / 100)) ^ 4 * inverseRadius8 (13157 - 1) /
            envelopeGap 13157 (61 / 100) 166 (17 / (100 * 13157)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13157

namespace BstLean.Part266.Row13157
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13157 166 ≤ (4195042289 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13157 166 ≤ (1399537109 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (336379293 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13157 166 ≤ (412180827 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 13157 166 ≤ (586517579 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13157 166 ≤ (428596873 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (428593141 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (428593141 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (130301177 / 100000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (770326773 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1797281 / 500000000) : ℝ) ≤ √(17 / (100 * 13157) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13157) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1035124559 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4512156791 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13157) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13157) ≤ (5374377 / 50000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13157) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13157 * (166 : ℝ) ^ 2 + 26 / (10 * 13157) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13157) : ℝ)) (tA 13157 * 166 ^ 2 + 26 / (10 * 13157)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1797281 / 500000000))) * ((428593141 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1797281 / 500000000)) ^ 3) * ((130301177 / 100000000000000000000000))) + ((770326773 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1797281 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13157) : ℝ)) d.D d.V d.P (√(tA 13157) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1797281 / 500000000)) ^ 2 * (((1035124559 / 500000000000000)) * ((4512156791 / 125000000000000000)))) + ((770326773 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13157) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1797281 / 500000000)) * ((428593141 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13157) : ℝ)) (tA 13157 * 166 ^ 2 + 26 / (10 * 13157)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((428593141 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1797281 / 500000000)) ^ 2) * ((130301177 / 100000000000000000000000)) + ((770326773 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13157) : ℝ)) (√(26 / (10 * 13157) : ℝ)) d.D d.V d.P (√(tA 13157) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1797281 / 500000000)) * (((1035124559 / 500000000000000)) * ((4512156791 / 125000000000000000))) + ((770326773 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13157) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((428593141 / 100000000000000000000) : ℝ) + ((770326773 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13157

namespace BstLean.Part266.Row13157
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13157 166 ∧
    0 ≤ (tableEnvelope C).f1 13157 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13157 166 ∧
    0 ≤ (tableEnvelope C).w1 13157 166 ∧ 0 ≤ (tableEnvelope C).w2 13157 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13157 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13157 166 ∧ 0 ≤ d.f1 13157 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13157 166 ∧ 0 ≤ d.w1 13157 166 ∧ 0 ≤ d.w2 13157 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13157 ≤ 2 * (228 / 100 : ℝ) / 13157 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13157 ≤ 2 * (370 / 100 : ℝ) / 13157 := by
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
    (completeRAData (tableEnvelope C) 13157 166).locationBound 13157 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13157 166).energyBound 13157 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13157 166) (d.f1 13157 166) d.f2 ≤
      32 * (((4195042289 / 1000000000000000000) : ℝ) + (1399537109 / 1000000000000000000) + (336379293 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13157 166) (d.w1 13157 166)
      (d.w2 13157 166) ≤
      32 * (((412180827 / 25000000000000000000) : ℝ) + (586517579 / 50000000000000000000) + (428596873 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13157 166) (d.f1 13157 166) d.f2 ≤
      ((4195042289 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4195042289 / 1000000000000000000)) * ((1399537109 / 1000000000000000000)) * (126 / 100) +
      2 * (((1399537109 / 1000000000000000000)) ^ 2 + 2 * ((4195042289 / 1000000000000000000)) * ((336379293 / 1000000000000000000))) +
      6 * ((1399537109 / 1000000000000000000)) * ((336379293 / 1000000000000000000)) * (126 / 100) + 8 * ((336379293 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13157 166) (d.f1 13157 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13157 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13157 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13157 166) (d.f1 13157 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13157 166) (d.w1 13157 166) (d.w2 13157 166)
  have hwexpr0 : 0 ≤ d.w0 13157 166 + d.w1 13157 166 * √(π / 2) +
      2 * d.w2 13157 166 + energyR16 13157 *
      radiusPolynomialRoot16 (d.w0 13157 166) (d.w1 13157 166) (d.w2 13157 166) := by
    positivity
  constructor
  · change (13157 : ℝ) ^ 8 * (mA 13157 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13157 166) (d.f1 13157 166) d.f2 + locationR16 13157 *
        radiusPolynomialRoot16 (d.f0 13157 166) (d.f1 13157 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13157 : ℝ) ^ 8 * (mA 13157 : ℝ) ^ 8 *
        ((((4195042289 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4195042289 / 1000000000000000000)) * ((1399537109 / 1000000000000000000)) * (126 / 100) +
          2 * (((1399537109 / 1000000000000000000)) ^ 2 + 2 * ((4195042289 / 1000000000000000000)) * ((336379293 / 1000000000000000000))) +
          6 * ((1399537109 / 1000000000000000000)) * ((336379293 / 1000000000000000000)) * (126 / 100) + 8 * ((336379293 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13157) *
          (32 * (((4195042289 / 1000000000000000000) : ℝ) + (1399537109 / 1000000000000000000) + (336379293 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13157 : ℝ) ^ 16 *
      (d.w0 13157 166 + d.w1 13157 166 * √(π / 2) + 2 * d.w2 13157 166 +
        energyR16 13157 * radiusPolynomialRoot16 (d.w0 13157 166) (d.w1 13157 166)
          (d.w2 13157 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13157 : ℝ) ^ 16 *
        (((412180827 / 25000000000000000000) : ℝ) + ((586517579 / 50000000000000000000)) * (126 / 100) + 2 * ((428596873 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13157) *
          (32 * (((412180827 / 25000000000000000000) : ℝ) + (586517579 / 50000000000000000000) + (428596873 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13157

/-! A coarse bound on the actual paper statistics constant at dimension 13158. -/
namespace BstLean.Part266.Row13158
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13156 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13156 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13156 128 ≤ (13410 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13410 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13158) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13158 : ℕ))
    (by norm_num : (13158 : ℕ) ≤ 16384)
  have ht : paperTail256 13158 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13158 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13158 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13158 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13158 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13158 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13156 128 * √(2 / (13158 : ℝ)) *
      (√(13158 : ℝ) + paperT0 13158 + paperTail256 13158) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13158 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13158 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13158 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13156 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13156 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13158 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13158

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13158
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13158 (61 / 100) 166 (17 / (100 * 13158)) (26 / (10 * 13158)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13158 (61 / 100) 166 (17 / (100 * 13158)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (17139817 / 4000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (162826961 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3849270689 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13158 / 13158 * (61 / 100)) ^ 4 * inverseRadius8 (13158 - 1) /
            envelopeGap 13158 (61 / 100) 166 (17 / (100 * 13158)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13158

namespace BstLean.Part266.Row13158
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13158 166 ≤ (20971233 / 5000000000000000)
  f1 : (tableEnvelope C).f1 13158 166 ≤ (1399271513 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (336315419 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13158 166 ≤ (1648347687 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13158 166 ≤ (1172767847 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13158 166 ≤ (214249577 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (17139817 / 4000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (17139817 / 4000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (162826961 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3849270689 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((143777 / 40000000) : ℝ) ≤ √(17 / (100 * 13158) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13158) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (129375819 / 62500000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18045883797 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13158) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13158) ≤ (107479371 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13158) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13158 * (166 : ℝ) ^ 2 + 26 / (10 * 13158) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13158) : ℝ)) (tA 13158 * 166 ^ 2 + 26 / (10 * 13158)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((143777 / 40000000))) * ((17139817 / 4000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((143777 / 40000000)) ^ 3) * ((162826961 / 125000000000000000000000))) + ((3849270689 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((143777 / 40000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13158) : ℝ)) d.D d.V d.P (√(tA 13158) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((143777 / 40000000)) ^ 2 * (((129375819 / 62500000000000)) * ((18045883797 / 500000000000000000)))) + ((3849270689 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13158) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((143777 / 40000000)) * ((17139817 / 4000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13158) : ℝ)) (tA 13158 * 166 ^ 2 + 26 / (10 * 13158)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((17139817 / 4000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((143777 / 40000000)) ^ 2) * ((162826961 / 125000000000000000000000)) + ((3849270689 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13158) : ℝ)) (√(26 / (10 * 13158) : ℝ)) d.D d.V d.P (√(tA 13158) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((143777 / 40000000)) * (((129375819 / 62500000000000)) * ((18045883797 / 500000000000000000))) + ((3849270689 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13158) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((17139817 / 4000000000000000000) : ℝ) + ((3849270689 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13158

namespace BstLean.Part266.Row13158
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13158 166 ∧
    0 ≤ (tableEnvelope C).f1 13158 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13158 166 ∧
    0 ≤ (tableEnvelope C).w1 13158 166 ∧ 0 ≤ (tableEnvelope C).w2 13158 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13158 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13158 166 ∧ 0 ≤ d.f1 13158 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13158 166 ∧ 0 ≤ d.w1 13158 166 ∧ 0 ≤ d.w2 13158 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13158 ≤ 2 * (228 / 100 : ℝ) / 13158 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13158 ≤ 2 * (370 / 100 : ℝ) / 13158 := by
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
    (completeRAData (tableEnvelope C) 13158 166).locationBound 13158 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13158 166).energyBound 13158 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13158 166) (d.f1 13158 166) d.f2 ≤
      32 * (((20971233 / 5000000000000000) : ℝ) + (1399271513 / 1000000000000000000) + (336315419 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13158 166) (d.w1 13158 166)
      (d.w2 13158 166) ≤
      32 * (((1648347687 / 100000000000000000000) : ℝ) + (1172767847 / 100000000000000000000) + (214249577 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13158 166) (d.f1 13158 166) d.f2 ≤
      ((20971233 / 5000000000000000) : ℝ) ^ 2 + 2 * ((20971233 / 5000000000000000)) * ((1399271513 / 1000000000000000000)) * (126 / 100) +
      2 * (((1399271513 / 1000000000000000000)) ^ 2 + 2 * ((20971233 / 5000000000000000)) * ((336315419 / 1000000000000000000))) +
      6 * ((1399271513 / 1000000000000000000)) * ((336315419 / 1000000000000000000)) * (126 / 100) + 8 * ((336315419 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13158 166) (d.f1 13158 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13158 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13158 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13158 166) (d.f1 13158 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13158 166) (d.w1 13158 166) (d.w2 13158 166)
  have hwexpr0 : 0 ≤ d.w0 13158 166 + d.w1 13158 166 * √(π / 2) +
      2 * d.w2 13158 166 + energyR16 13158 *
      radiusPolynomialRoot16 (d.w0 13158 166) (d.w1 13158 166) (d.w2 13158 166) := by
    positivity
  constructor
  · change (13158 : ℝ) ^ 8 * (mA 13158 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13158 166) (d.f1 13158 166) d.f2 + locationR16 13158 *
        radiusPolynomialRoot16 (d.f0 13158 166) (d.f1 13158 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13158 : ℝ) ^ 8 * (mA 13158 : ℝ) ^ 8 *
        ((((20971233 / 5000000000000000) : ℝ) ^ 2 + 2 * ((20971233 / 5000000000000000)) * ((1399271513 / 1000000000000000000)) * (126 / 100) +
          2 * (((1399271513 / 1000000000000000000)) ^ 2 + 2 * ((20971233 / 5000000000000000)) * ((336315419 / 1000000000000000000))) +
          6 * ((1399271513 / 1000000000000000000)) * ((336315419 / 1000000000000000000)) * (126 / 100) + 8 * ((336315419 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13158) *
          (32 * (((20971233 / 5000000000000000) : ℝ) + (1399271513 / 1000000000000000000) + (336315419 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13158 : ℝ) ^ 16 *
      (d.w0 13158 166 + d.w1 13158 166 * √(π / 2) + 2 * d.w2 13158 166 +
        energyR16 13158 * radiusPolynomialRoot16 (d.w0 13158 166) (d.w1 13158 166)
          (d.w2 13158 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13158 : ℝ) ^ 16 *
        (((1648347687 / 100000000000000000000) : ℝ) + ((1172767847 / 100000000000000000000)) * (126 / 100) + 2 * ((214249577 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13158) *
          (32 * (((1648347687 / 100000000000000000000) : ℝ) + (1172767847 / 100000000000000000000) + (214249577 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13158

/-! A coarse bound on the actual paper statistics constant at dimension 13159. -/
namespace BstLean.Part266.Row13159
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13157 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13157 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13157 128 ≤ (13411 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13411 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13159) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13159 : ℕ))
    (by norm_num : (13159 : ℕ) ≤ 16384)
  have ht : paperTail256 13159 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13159 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13159 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13159 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13159 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13159 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13157 128 * √(2 / (13159 : ℝ)) *
      (√(13159 : ℝ) + paperT0 13159 + paperTail256 13159) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13159 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13159 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13159 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13157 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13157 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13159 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13159

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13159
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13159 (61 / 100) 166 (17 / (100 * 13159)) (26 / (10 * 13159)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13159 (61 / 100) 166 (17 / (100 * 13159)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (428397739 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (325554939 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (769381829 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13159 / 13159 * (61 / 100)) ^ 4 * inverseRadius8 (13159 - 1) /
            envelopeGap 13159 (61 / 100) 166 (17 / (100 * 13159)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13159

namespace BstLean.Part266.Row13159
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13159 166 ≤ (2096723903 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13159 166 ≤ (699502611 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (33625147 / 100000000000000000)
  w0 : (tableEnvelope C).w0 13159 166 ≤ (1647971511 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13159 166 ≤ (146562537 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 13159 166 ≤ (214200733 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (428397739 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (428397739 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (325554939 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (769381829 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3594289 / 1000000000) : ℝ) ≤ √(17 / (100 * 13159) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13159) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (129361071 / 62500000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36086282103 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13159) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13159) ≤ (26867801 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13159) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13159 * (166 : ℝ) ^ 2 + 26 / (10 * 13159) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13159) : ℝ)) (tA 13159 * 166 ^ 2 + 26 / (10 * 13159)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3594289 / 1000000000))) * ((428397739 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3594289 / 1000000000)) ^ 3) * ((325554939 / 250000000000000000000000))) + ((769381829 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3594289 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13159) : ℝ)) d.D d.V d.P (√(tA 13159) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3594289 / 1000000000)) ^ 2 * (((129361071 / 62500000000000)) * ((36086282103 / 1000000000000000000)))) + ((769381829 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13159) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3594289 / 1000000000)) * ((428397739 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13159) : ℝ)) (tA 13159 * 166 ^ 2 + 26 / (10 * 13159)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((428397739 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3594289 / 1000000000)) ^ 2) * ((325554939 / 250000000000000000000000)) + ((769381829 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13159) : ℝ)) (√(26 / (10 * 13159) : ℝ)) d.D d.V d.P (√(tA 13159) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3594289 / 1000000000)) * (((129361071 / 62500000000000)) * ((36086282103 / 1000000000000000000))) + ((769381829 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13159) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((428397739 / 100000000000000000000) : ℝ) + ((769381829 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13159

namespace BstLean.Part266.Row13159
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13159 166 ∧
    0 ≤ (tableEnvelope C).f1 13159 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13159 166 ∧
    0 ≤ (tableEnvelope C).w1 13159 166 ∧ 0 ≤ (tableEnvelope C).w2 13159 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13159 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13159 166 ∧ 0 ≤ d.f1 13159 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13159 166 ∧ 0 ≤ d.w1 13159 166 ∧ 0 ≤ d.w2 13159 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13159 ≤ 2 * (228 / 100 : ℝ) / 13159 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13159 ≤ 2 * (370 / 100 : ℝ) / 13159 := by
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
    (completeRAData (tableEnvelope C) 13159 166).locationBound 13159 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13159 166).energyBound 13159 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13159 166) (d.f1 13159 166) d.f2 ≤
      32 * (((2096723903 / 500000000000000000) : ℝ) + (699502611 / 500000000000000000) + (33625147 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13159 166) (d.w1 13159 166)
      (d.w2 13159 166) ≤
      32 * (((1647971511 / 100000000000000000000) : ℝ) + (146562537 / 12500000000000000000) + (214200733 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13159 166) (d.f1 13159 166) d.f2 ≤
      ((2096723903 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2096723903 / 500000000000000000)) * ((699502611 / 500000000000000000)) * (126 / 100) +
      2 * (((699502611 / 500000000000000000)) ^ 2 + 2 * ((2096723903 / 500000000000000000)) * ((33625147 / 100000000000000000))) +
      6 * ((699502611 / 500000000000000000)) * ((33625147 / 100000000000000000)) * (126 / 100) + 8 * ((33625147 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13159 166) (d.f1 13159 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13159 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13159 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13159 166) (d.f1 13159 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13159 166) (d.w1 13159 166) (d.w2 13159 166)
  have hwexpr0 : 0 ≤ d.w0 13159 166 + d.w1 13159 166 * √(π / 2) +
      2 * d.w2 13159 166 + energyR16 13159 *
      radiusPolynomialRoot16 (d.w0 13159 166) (d.w1 13159 166) (d.w2 13159 166) := by
    positivity
  constructor
  · change (13159 : ℝ) ^ 8 * (mA 13159 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13159 166) (d.f1 13159 166) d.f2 + locationR16 13159 *
        radiusPolynomialRoot16 (d.f0 13159 166) (d.f1 13159 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13159 : ℝ) ^ 8 * (mA 13159 : ℝ) ^ 8 *
        ((((2096723903 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2096723903 / 500000000000000000)) * ((699502611 / 500000000000000000)) * (126 / 100) +
          2 * (((699502611 / 500000000000000000)) ^ 2 + 2 * ((2096723903 / 500000000000000000)) * ((33625147 / 100000000000000000))) +
          6 * ((699502611 / 500000000000000000)) * ((33625147 / 100000000000000000)) * (126 / 100) + 8 * ((33625147 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13159) *
          (32 * (((2096723903 / 500000000000000000) : ℝ) + (699502611 / 500000000000000000) + (33625147 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13159 : ℝ) ^ 16 *
      (d.w0 13159 166 + d.w1 13159 166 * √(π / 2) + 2 * d.w2 13159 166 +
        energyR16 13159 * radiusPolynomialRoot16 (d.w0 13159 166) (d.w1 13159 166)
          (d.w2 13159 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13159 : ℝ) ^ 16 *
        (((1647971511 / 100000000000000000000) : ℝ) + ((146562537 / 12500000000000000000)) * (126 / 100) + 2 * ((214200733 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13159) *
          (32 * (((1647971511 / 100000000000000000000) : ℝ) + (146562537 / 12500000000000000000) + (214200733 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13159

/-! A coarse bound on the actual paper statistics constant at dimension 13160. -/
namespace BstLean.Part266.Row13160
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13158 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13158 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13158 128 ≤ (13412 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13412 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13160) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13160 : ℕ))
    (by norm_num : (13160 : ℕ) ≤ 16384)
  have ht : paperTail256 13160 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13160 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13160 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13160 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13160 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13160 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13158 128 * √(2 / (13160 : ℝ)) *
      (√(13160 : ℝ) + paperT0 13160 + paperTail256 13160) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13160 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13160 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13160 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13158 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13158 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13160 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13160

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13160
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13160 (61 / 100) 166 (17 / (100 * 13160)) (26 / (10 * 13160)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13160 (61 / 100) 166 (17 / (100 * 13160)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (214150041 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (52072959 / 40000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (240284327 / 62500000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13160 / 13160 * (61 / 100)) ^ 4 * inverseRadius8 (13160 - 1) /
            envelopeGap 13160 (61 / 100) 166 (17 / (100 * 13160)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13160

namespace BstLean.Part266.Row13160
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13160 166 ≤ (838530529 / 200000000000000000)
  f1 : (tableEnvelope C).f1 13160 166 ≤ (87421237 / 62500000000000000)
  f2 : (tableEnvelope C).f2 ≤ (336187633 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13160 166 ≤ (1647596139 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13160 166 ≤ (586116579 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13160 166 ≤ (428303807 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (214150041 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (214150041 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (52072959 / 40000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (240284327 / 62500000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((449269 / 125000000) : ℝ) ≤ √(17 / (100 * 13160) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13160) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2069541211 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36080797871 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13160) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13160) ≤ (107463037 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13160) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13160 * (166 : ℝ) ^ 2 + 26 / (10 * 13160) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13160) : ℝ)) (tA 13160 * 166 ^ 2 + 26 / (10 * 13160)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((449269 / 125000000))) * ((214150041 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((449269 / 125000000)) ^ 3) * ((52072959 / 40000000000000000000000))) + ((240284327 / 62500000000000000000000)) * (3 / 2 * (39895 / 100000) / ((449269 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13160) : ℝ)) d.D d.V d.P (√(tA 13160) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((449269 / 125000000)) ^ 2 * (((2069541211 / 1000000000000000)) * ((36080797871 / 1000000000000000000)))) + ((240284327 / 62500000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13160) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((449269 / 125000000)) * ((214150041 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13160) : ℝ)) (tA 13160 * 166 ^ 2 + 26 / (10 * 13160)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((214150041 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((449269 / 125000000)) ^ 2) * ((52072959 / 40000000000000000000000)) + ((240284327 / 62500000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13160) : ℝ)) (√(26 / (10 * 13160) : ℝ)) d.D d.V d.P (√(tA 13160) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((449269 / 125000000)) * (((2069541211 / 1000000000000000)) * ((36080797871 / 1000000000000000000))) + ((240284327 / 62500000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13160) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((214150041 / 50000000000000000000) : ℝ) + ((240284327 / 62500000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13160

namespace BstLean.Part266.Row13160
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13160 166 ∧
    0 ≤ (tableEnvelope C).f1 13160 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13160 166 ∧
    0 ≤ (tableEnvelope C).w1 13160 166 ∧ 0 ≤ (tableEnvelope C).w2 13160 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13160 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13160 166 ∧ 0 ≤ d.f1 13160 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13160 166 ∧ 0 ≤ d.w1 13160 166 ∧ 0 ≤ d.w2 13160 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13160 ≤ 2 * (228 / 100 : ℝ) / 13160 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13160 ≤ 2 * (370 / 100 : ℝ) / 13160 := by
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
    (completeRAData (tableEnvelope C) 13160 166).locationBound 13160 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13160 166).energyBound 13160 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13160 166) (d.f1 13160 166) d.f2 ≤
      32 * (((838530529 / 200000000000000000) : ℝ) + (87421237 / 62500000000000000) + (336187633 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13160 166) (d.w1 13160 166)
      (d.w2 13160 166) ≤
      32 * (((1647596139 / 100000000000000000000) : ℝ) + (586116579 / 50000000000000000000) + (428303807 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13160 166) (d.f1 13160 166) d.f2 ≤
      ((838530529 / 200000000000000000) : ℝ) ^ 2 + 2 * ((838530529 / 200000000000000000)) * ((87421237 / 62500000000000000)) * (126 / 100) +
      2 * (((87421237 / 62500000000000000)) ^ 2 + 2 * ((838530529 / 200000000000000000)) * ((336187633 / 1000000000000000000))) +
      6 * ((87421237 / 62500000000000000)) * ((336187633 / 1000000000000000000)) * (126 / 100) + 8 * ((336187633 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13160 166) (d.f1 13160 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13160 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13160 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13160 166) (d.f1 13160 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13160 166) (d.w1 13160 166) (d.w2 13160 166)
  have hwexpr0 : 0 ≤ d.w0 13160 166 + d.w1 13160 166 * √(π / 2) +
      2 * d.w2 13160 166 + energyR16 13160 *
      radiusPolynomialRoot16 (d.w0 13160 166) (d.w1 13160 166) (d.w2 13160 166) := by
    positivity
  constructor
  · change (13160 : ℝ) ^ 8 * (mA 13160 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13160 166) (d.f1 13160 166) d.f2 + locationR16 13160 *
        radiusPolynomialRoot16 (d.f0 13160 166) (d.f1 13160 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13160 : ℝ) ^ 8 * (mA 13160 : ℝ) ^ 8 *
        ((((838530529 / 200000000000000000) : ℝ) ^ 2 + 2 * ((838530529 / 200000000000000000)) * ((87421237 / 62500000000000000)) * (126 / 100) +
          2 * (((87421237 / 62500000000000000)) ^ 2 + 2 * ((838530529 / 200000000000000000)) * ((336187633 / 1000000000000000000))) +
          6 * ((87421237 / 62500000000000000)) * ((336187633 / 1000000000000000000)) * (126 / 100) + 8 * ((336187633 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13160) *
          (32 * (((838530529 / 200000000000000000) : ℝ) + (87421237 / 62500000000000000) + (336187633 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13160 : ℝ) ^ 16 *
      (d.w0 13160 166 + d.w1 13160 166 * √(π / 2) + 2 * d.w2 13160 166 +
        energyR16 13160 * radiusPolynomialRoot16 (d.w0 13160 166) (d.w1 13160 166)
          (d.w2 13160 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13160 : ℝ) ^ 16 *
        (((1647596139 / 100000000000000000000) : ℝ) + ((586116579 / 50000000000000000000)) * (126 / 100) + 2 * ((428303807 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13160) *
          (32 * (((1647596139 / 100000000000000000000) : ℝ) + (586116579 / 50000000000000000000) + (428303807 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13160

/-! A coarse bound on the actual paper statistics constant at dimension 13161. -/
namespace BstLean.Part266.Row13161
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13159 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13159 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13159 128 ≤ (13413 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13413 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13161) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13161 : ℕ))
    (by norm_num : (13161 : ℕ) ≤ 16384)
  have ht : paperTail256 13161 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13161 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13161 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13161 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13161 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13161 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13159 128 * √(2 / (13161 : ℝ)) *
      (√(13161 : ℝ) + paperT0 13161 + paperTail256 13161) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13161 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13161 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13161 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13159 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13159 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13161 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13161

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13161
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13161 (61 / 100) 166 (17 / (100 * 13161)) (26 / (10 * 13161)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13161 (61 / 100) 166 (17 / (100 * 13161)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (85640491 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (162678543 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (76843819 / 20000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13161 / 13161 * (61 / 100)) ^ 4 * inverseRadius8 (13161 - 1) /
            envelopeGap 13161 (61 / 100) 166 (17 / (100 * 13161)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13161

namespace BstLean.Part266.Row13161
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13161 166 ≤ (209592719 / 50000000000000000)
  f1 : (tableEnvelope C).f1 13161 166 ≤ (699236833 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (336123721 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13161 166 ≤ (1647220213 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13161 166 ≤ (1171965779 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13161 166 ≤ (428206177 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (85640491 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (85640491 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (162678543 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (76843819 / 20000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((112313 / 31250000) : ℝ) ≤ √(17 / (100 * 13161) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13161) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2069305331 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7215062977 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13161) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13161) ≤ (13431859 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13161) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13161 * (166 : ℝ) ^ 2 + 26 / (10 * 13161) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13161) : ℝ)) (tA 13161 * 166 ^ 2 + 26 / (10 * 13161)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((112313 / 31250000))) * ((85640491 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((112313 / 31250000)) ^ 3) * ((162678543 / 125000000000000000000000))) + ((76843819 / 20000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((112313 / 31250000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13161) : ℝ)) d.D d.V d.P (√(tA 13161) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((112313 / 31250000)) ^ 2 * (((2069305331 / 1000000000000000)) * ((7215062977 / 200000000000000000)))) + ((76843819 / 20000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13161) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((112313 / 31250000)) * ((85640491 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13161) : ℝ)) (tA 13161 * 166 ^ 2 + 26 / (10 * 13161)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((85640491 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((112313 / 31250000)) ^ 2) * ((162678543 / 125000000000000000000000)) + ((76843819 / 20000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13161) : ℝ)) (√(26 / (10 * 13161) : ℝ)) d.D d.V d.P (√(tA 13161) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((112313 / 31250000)) * (((2069305331 / 1000000000000000)) * ((7215062977 / 200000000000000000))) + ((76843819 / 20000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13161) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((85640491 / 20000000000000000000) : ℝ) + ((76843819 / 20000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13161

namespace BstLean.Part266.Row13161
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13161 166 ∧
    0 ≤ (tableEnvelope C).f1 13161 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13161 166 ∧
    0 ≤ (tableEnvelope C).w1 13161 166 ∧ 0 ≤ (tableEnvelope C).w2 13161 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13161 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13161 166 ∧ 0 ≤ d.f1 13161 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13161 166 ∧ 0 ≤ d.w1 13161 166 ∧ 0 ≤ d.w2 13161 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13161 ≤ 2 * (228 / 100 : ℝ) / 13161 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13161 ≤ 2 * (370 / 100 : ℝ) / 13161 := by
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
    (completeRAData (tableEnvelope C) 13161 166).locationBound 13161 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13161 166).energyBound 13161 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13161 166) (d.f1 13161 166) d.f2 ≤
      32 * (((209592719 / 50000000000000000) : ℝ) + (699236833 / 500000000000000000) + (336123721 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13161 166) (d.w1 13161 166)
      (d.w2 13161 166) ≤
      32 * (((1647220213 / 100000000000000000000) : ℝ) + (1171965779 / 100000000000000000000) + (428206177 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13161 166) (d.f1 13161 166) d.f2 ≤
      ((209592719 / 50000000000000000) : ℝ) ^ 2 + 2 * ((209592719 / 50000000000000000)) * ((699236833 / 500000000000000000)) * (126 / 100) +
      2 * (((699236833 / 500000000000000000)) ^ 2 + 2 * ((209592719 / 50000000000000000)) * ((336123721 / 1000000000000000000))) +
      6 * ((699236833 / 500000000000000000)) * ((336123721 / 1000000000000000000)) * (126 / 100) + 8 * ((336123721 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13161 166) (d.f1 13161 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13161 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13161 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13161 166) (d.f1 13161 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13161 166) (d.w1 13161 166) (d.w2 13161 166)
  have hwexpr0 : 0 ≤ d.w0 13161 166 + d.w1 13161 166 * √(π / 2) +
      2 * d.w2 13161 166 + energyR16 13161 *
      radiusPolynomialRoot16 (d.w0 13161 166) (d.w1 13161 166) (d.w2 13161 166) := by
    positivity
  constructor
  · change (13161 : ℝ) ^ 8 * (mA 13161 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13161 166) (d.f1 13161 166) d.f2 + locationR16 13161 *
        radiusPolynomialRoot16 (d.f0 13161 166) (d.f1 13161 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13161 : ℝ) ^ 8 * (mA 13161 : ℝ) ^ 8 *
        ((((209592719 / 50000000000000000) : ℝ) ^ 2 + 2 * ((209592719 / 50000000000000000)) * ((699236833 / 500000000000000000)) * (126 / 100) +
          2 * (((699236833 / 500000000000000000)) ^ 2 + 2 * ((209592719 / 50000000000000000)) * ((336123721 / 1000000000000000000))) +
          6 * ((699236833 / 500000000000000000)) * ((336123721 / 1000000000000000000)) * (126 / 100) + 8 * ((336123721 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13161) *
          (32 * (((209592719 / 50000000000000000) : ℝ) + (699236833 / 500000000000000000) + (336123721 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13161 : ℝ) ^ 16 *
      (d.w0 13161 166 + d.w1 13161 166 * √(π / 2) + 2 * d.w2 13161 166 +
        energyR16 13161 * radiusPolynomialRoot16 (d.w0 13161 166) (d.w1 13161 166)
          (d.w2 13161 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13161 : ℝ) ^ 16 *
        (((1647220213 / 100000000000000000000) : ℝ) + ((1171965779 / 100000000000000000000)) * (126 / 100) + 2 * ((428206177 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13161) *
          (32 * (((1647220213 / 100000000000000000000) : ℝ) + (1171965779 / 100000000000000000000) + (428206177 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13161

/-! A coarse bound on the actual paper statistics constant at dimension 13162. -/
namespace BstLean.Part266.Row13162
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13160 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13160 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13160 128 ≤ (13414 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13414 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13162) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13162 : ℕ))
    (by norm_num : (13162 : ℕ) ≤ 16384)
  have ht : paperTail256 13162 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13162 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13162 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13162 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13162 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13162 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13160 128 * √(2 / (13162 : ℝ)) *
      (√(13162 : ℝ) + paperT0 13162 + paperTail256 13162) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13162 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13162 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13162 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13160 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13160 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13162 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13162

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13162
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13162 (61 / 100) 166 (17 / (100 * 13162)) (26 / (10 * 13162)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13162 (61 / 100) 166 (17 / (100 * 13162)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (214052429 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1301032863 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (479979287 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13162 / 13162 * (61 / 100)) ^ 4 * inverseRadius8 (13162 - 1) /
            envelopeGap 13162 (61 / 100) 166 (17 / (100 * 13162)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13162

namespace BstLean.Part266.Row13162
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13162 166 ≤ (2095529873 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13162 166 ≤ (699104201 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (336059921 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13162 166 ≤ (164684509 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 13162 166 ≤ (1171698813 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13162 166 ≤ (214054289 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (214052429 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (214052429 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1301032863 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (479979287 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3593879 / 1000000000) : ℝ) ≤ √(17 / (100 * 13162) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13162) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2069069497 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4508729143 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13162) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13162) ≤ (26861677 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13162) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13162 * (166 : ℝ) ^ 2 + 26 / (10 * 13162) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13162) : ℝ)) (tA 13162 * 166 ^ 2 + 26 / (10 * 13162)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3593879 / 1000000000))) * ((214052429 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3593879 / 1000000000)) ^ 3) * ((1301032863 / 1000000000000000000000000))) + ((479979287 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3593879 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13162) : ℝ)) d.D d.V d.P (√(tA 13162) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3593879 / 1000000000)) ^ 2 * (((2069069497 / 1000000000000000)) * ((4508729143 / 125000000000000000)))) + ((479979287 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13162) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3593879 / 1000000000)) * ((214052429 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13162) : ℝ)) (tA 13162 * 166 ^ 2 + 26 / (10 * 13162)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((214052429 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3593879 / 1000000000)) ^ 2) * ((1301032863 / 1000000000000000000000000)) + ((479979287 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13162) : ℝ)) (√(26 / (10 * 13162) : ℝ)) d.D d.V d.P (√(tA 13162) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3593879 / 1000000000)) * (((2069069497 / 1000000000000000)) * ((4508729143 / 125000000000000000))) + ((479979287 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13162) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((214052429 / 50000000000000000000) : ℝ) + ((479979287 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13162

namespace BstLean.Part266.Row13162
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13162 166 ∧
    0 ≤ (tableEnvelope C).f1 13162 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13162 166 ∧
    0 ≤ (tableEnvelope C).w1 13162 166 ∧ 0 ≤ (tableEnvelope C).w2 13162 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13162 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13162 166 ∧ 0 ≤ d.f1 13162 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13162 166 ∧ 0 ≤ d.w1 13162 166 ∧ 0 ≤ d.w2 13162 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13162 ≤ 2 * (228 / 100 : ℝ) / 13162 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13162 ≤ 2 * (370 / 100 : ℝ) / 13162 := by
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
    (completeRAData (tableEnvelope C) 13162 166).locationBound 13162 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13162 166).energyBound 13162 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13162 166) (d.f1 13162 166) d.f2 ≤
      32 * (((2095529873 / 500000000000000000) : ℝ) + (699104201 / 500000000000000000) + (336059921 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13162 166) (d.w1 13162 166)
      (d.w2 13162 166) ≤
      32 * (((164684509 / 10000000000000000000) : ℝ) + (1171698813 / 100000000000000000000) + (214054289 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13162 166) (d.f1 13162 166) d.f2 ≤
      ((2095529873 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2095529873 / 500000000000000000)) * ((699104201 / 500000000000000000)) * (126 / 100) +
      2 * (((699104201 / 500000000000000000)) ^ 2 + 2 * ((2095529873 / 500000000000000000)) * ((336059921 / 1000000000000000000))) +
      6 * ((699104201 / 500000000000000000)) * ((336059921 / 1000000000000000000)) * (126 / 100) + 8 * ((336059921 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13162 166) (d.f1 13162 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13162 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13162 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13162 166) (d.f1 13162 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13162 166) (d.w1 13162 166) (d.w2 13162 166)
  have hwexpr0 : 0 ≤ d.w0 13162 166 + d.w1 13162 166 * √(π / 2) +
      2 * d.w2 13162 166 + energyR16 13162 *
      radiusPolynomialRoot16 (d.w0 13162 166) (d.w1 13162 166) (d.w2 13162 166) := by
    positivity
  constructor
  · change (13162 : ℝ) ^ 8 * (mA 13162 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13162 166) (d.f1 13162 166) d.f2 + locationR16 13162 *
        radiusPolynomialRoot16 (d.f0 13162 166) (d.f1 13162 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13162 : ℝ) ^ 8 * (mA 13162 : ℝ) ^ 8 *
        ((((2095529873 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2095529873 / 500000000000000000)) * ((699104201 / 500000000000000000)) * (126 / 100) +
          2 * (((699104201 / 500000000000000000)) ^ 2 + 2 * ((2095529873 / 500000000000000000)) * ((336059921 / 1000000000000000000))) +
          6 * ((699104201 / 500000000000000000)) * ((336059921 / 1000000000000000000)) * (126 / 100) + 8 * ((336059921 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13162) *
          (32 * (((2095529873 / 500000000000000000) : ℝ) + (699104201 / 500000000000000000) + (336059921 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13162 : ℝ) ^ 16 *
      (d.w0 13162 166 + d.w1 13162 166 * √(π / 2) + 2 * d.w2 13162 166 +
        energyR16 13162 * radiusPolynomialRoot16 (d.w0 13162 166) (d.w1 13162 166)
          (d.w2 13162 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13162 : ℝ) ^ 16 *
        (((164684509 / 10000000000000000000) : ℝ) + ((1171698813 / 100000000000000000000)) * (126 / 100) + 2 * ((214054289 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13162) *
          (32 * (((164684509 / 10000000000000000000) : ℝ) + (1171698813 / 100000000000000000000) + (214054289 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13162

/-! A coarse bound on the actual paper statistics constant at dimension 13163. -/
namespace BstLean.Part266.Row13163
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13161 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13161 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13161 128 ≤ (13415 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13415 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13163) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13163 : ℕ))
    (by norm_num : (13163 : ℕ) ≤ 16384)
  have ht : paperTail256 13163 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13163 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13163 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13163 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13163 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13163 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13161 128 * √(2 / (13163 : ℝ)) *
      (√(13163 : ℝ) + paperT0 13163 + paperTail256 13163) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13163 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13163 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13163 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13161 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13161 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13163 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13163

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13163
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13163 (61 / 100) 166 (17 / (100 * 13163)) (26 / (10 * 13163)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13163 (61 / 100) 166 (17 / (100 * 13163)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (42800729 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (325159383 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3837479271 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13163 / 13163 * (61 / 100)) ^ 4 * inverseRadius8 (13163 - 1) /
            envelopeGap 13163 (61 / 100) 166 (17 / (100 * 13163)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13163

namespace BstLean.Part266.Row13163
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13163 166 ≤ (4190262009 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13163 166 ≤ (1397942441 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (67199209 / 200000000000000000)
  w0 : (tableEnvelope C).w0 13163 166 ≤ (1646469413 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13163 166 ≤ (1171431607 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13163 166 ≤ (835959 / 195312500000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (42800729 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (42800729 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (325159383 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3837479271 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3593743 / 1000000000) : ℝ) ≤ √(17 / (100 * 13163) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13163) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1034416853 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (721287053 / 20000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13163) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13163) ≤ (21487709 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13163) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13163 * (166 : ℝ) ^ 2 + 26 / (10 * 13163) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13163) : ℝ)) (tA 13163 * 166 ^ 2 + 26 / (10 * 13163)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3593743 / 1000000000))) * ((42800729 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3593743 / 1000000000)) ^ 3) * ((325159383 / 250000000000000000000000))) + ((3837479271 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3593743 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13163) : ℝ)) d.D d.V d.P (√(tA 13163) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3593743 / 1000000000)) ^ 2 * (((1034416853 / 500000000000000)) * ((721287053 / 20000000000000000)))) + ((3837479271 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13163) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3593743 / 1000000000)) * ((42800729 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13163) : ℝ)) (tA 13163 * 166 ^ 2 + 26 / (10 * 13163)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((42800729 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3593743 / 1000000000)) ^ 2) * ((325159383 / 250000000000000000000000)) + ((3837479271 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13163) : ℝ)) (√(26 / (10 * 13163) : ℝ)) d.D d.V d.P (√(tA 13163) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3593743 / 1000000000)) * (((1034416853 / 500000000000000)) * ((721287053 / 20000000000000000))) + ((3837479271 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13163) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((42800729 / 10000000000000000000) : ℝ) + ((3837479271 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13163

namespace BstLean.Part266.Row13163
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13163 166 ∧
    0 ≤ (tableEnvelope C).f1 13163 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13163 166 ∧
    0 ≤ (tableEnvelope C).w1 13163 166 ∧ 0 ≤ (tableEnvelope C).w2 13163 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13163 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13163 166 ∧ 0 ≤ d.f1 13163 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13163 166 ∧ 0 ≤ d.w1 13163 166 ∧ 0 ≤ d.w2 13163 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13163 ≤ 2 * (228 / 100 : ℝ) / 13163 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13163 ≤ 2 * (370 / 100 : ℝ) / 13163 := by
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
    (completeRAData (tableEnvelope C) 13163 166).locationBound 13163 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13163 166).energyBound 13163 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13163 166) (d.f1 13163 166) d.f2 ≤
      32 * (((4190262009 / 1000000000000000000) : ℝ) + (1397942441 / 1000000000000000000) + (67199209 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13163 166) (d.w1 13163 166)
      (d.w2 13163 166) ≤
      32 * (((1646469413 / 100000000000000000000) : ℝ) + (1171431607 / 100000000000000000000) + (835959 / 195312500000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13163 166) (d.f1 13163 166) d.f2 ≤
      ((4190262009 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4190262009 / 1000000000000000000)) * ((1397942441 / 1000000000000000000)) * (126 / 100) +
      2 * (((1397942441 / 1000000000000000000)) ^ 2 + 2 * ((4190262009 / 1000000000000000000)) * ((67199209 / 200000000000000000))) +
      6 * ((1397942441 / 1000000000000000000)) * ((67199209 / 200000000000000000)) * (126 / 100) + 8 * ((67199209 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13163 166) (d.f1 13163 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13163 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13163 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13163 166) (d.f1 13163 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13163 166) (d.w1 13163 166) (d.w2 13163 166)
  have hwexpr0 : 0 ≤ d.w0 13163 166 + d.w1 13163 166 * √(π / 2) +
      2 * d.w2 13163 166 + energyR16 13163 *
      radiusPolynomialRoot16 (d.w0 13163 166) (d.w1 13163 166) (d.w2 13163 166) := by
    positivity
  constructor
  · change (13163 : ℝ) ^ 8 * (mA 13163 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13163 166) (d.f1 13163 166) d.f2 + locationR16 13163 *
        radiusPolynomialRoot16 (d.f0 13163 166) (d.f1 13163 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13163 : ℝ) ^ 8 * (mA 13163 : ℝ) ^ 8 *
        ((((4190262009 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4190262009 / 1000000000000000000)) * ((1397942441 / 1000000000000000000)) * (126 / 100) +
          2 * (((1397942441 / 1000000000000000000)) ^ 2 + 2 * ((4190262009 / 1000000000000000000)) * ((67199209 / 200000000000000000))) +
          6 * ((1397942441 / 1000000000000000000)) * ((67199209 / 200000000000000000)) * (126 / 100) + 8 * ((67199209 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13163) *
          (32 * (((4190262009 / 1000000000000000000) : ℝ) + (1397942441 / 1000000000000000000) + (67199209 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13163 : ℝ) ^ 16 *
      (d.w0 13163 166 + d.w1 13163 166 * √(π / 2) + 2 * d.w2 13163 166 +
        energyR16 13163 * radiusPolynomialRoot16 (d.w0 13163 166) (d.w1 13163 166)
          (d.w2 13163 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13163 : ℝ) ^ 16 *
        (((1646469413 / 100000000000000000000) : ℝ) + ((1171431607 / 100000000000000000000)) * (126 / 100) + 2 * ((835959 / 195312500000000000)) +
          (2 * (370 / 100 : ℝ) / 13163) *
          (32 * (((1646469413 / 100000000000000000000) : ℝ) + (1171431607 / 100000000000000000000) + (835959 / 195312500000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13163

/-! A coarse bound on the actual paper statistics constant at dimension 13164. -/
namespace BstLean.Part266.Row13164
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13162 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13162 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13162 128 ≤ (13416 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13416 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13164) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13164 : ℕ))
    (by norm_num : (13164 : ℕ) ≤ 16384)
  have ht : paperTail256 13164 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13164 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13164 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13164 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13164 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13164 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13162 128 * √(2 / (13164 : ℝ)) *
      (√(13164 : ℝ) + paperT0 13164 + paperTail256 13164) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13164 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13164 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13164 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13162 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13162 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13164 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13164

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13164
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13164 (61 / 100) 166 (17 / (100 * 13164)) (26 / (10 * 13164)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13164 (61 / 100) 166 (17 / (100 * 13164)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (53488719 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (81265147 / 62500000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3835125871 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13164 / 13164 * (61 / 100)) ^ 4 * inverseRadius8 (13164 - 1) /
            envelopeGap 13164 (61 / 100) 166 (17 / (100 * 13164)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13164

namespace BstLean.Part266.Row13164
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13164 166 ≤ (16365109 / 3906250000000000)
  f1 : (tableEnvelope C).f1 13164 166 ≤ (1397677341 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (167966141 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13164 166 ≤ (1646094539 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13164 166 ≤ (1171164813 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13164 166 ≤ (106978367 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (53488719 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (53488719 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (81265147 / 62500000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3835125871 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1796803 / 500000000) : ℝ) ≤ √(17 / (100 * 13164) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13164) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (51714949 / 25000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4507359177 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13164) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13164) ≤ (6714399 / 62500000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13164) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13164 * (166 : ℝ) ^ 2 + 26 / (10 * 13164) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13164) : ℝ)) (tA 13164 * 166 ^ 2 + 26 / (10 * 13164)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1796803 / 500000000))) * ((53488719 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1796803 / 500000000)) ^ 3) * ((81265147 / 62500000000000000000000))) + ((3835125871 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1796803 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13164) : ℝ)) d.D d.V d.P (√(tA 13164) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1796803 / 500000000)) ^ 2 * (((51714949 / 25000000000000)) * ((4507359177 / 125000000000000000)))) + ((3835125871 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13164) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1796803 / 500000000)) * ((53488719 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13164) : ℝ)) (tA 13164 * 166 ^ 2 + 26 / (10 * 13164)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((53488719 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1796803 / 500000000)) ^ 2) * ((81265147 / 62500000000000000000000)) + ((3835125871 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13164) : ℝ)) (√(26 / (10 * 13164) : ℝ)) d.D d.V d.P (√(tA 13164) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1796803 / 500000000)) * (((51714949 / 25000000000000)) * ((4507359177 / 125000000000000000))) + ((3835125871 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13164) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((53488719 / 12500000000000000000) : ℝ) + ((3835125871 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13164

namespace BstLean.Part266.Row13164
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13164 166 ∧
    0 ≤ (tableEnvelope C).f1 13164 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13164 166 ∧
    0 ≤ (tableEnvelope C).w1 13164 166 ∧ 0 ≤ (tableEnvelope C).w2 13164 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13164 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13164 166 ∧ 0 ≤ d.f1 13164 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13164 166 ∧ 0 ≤ d.w1 13164 166 ∧ 0 ≤ d.w2 13164 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13164 ≤ 2 * (228 / 100 : ℝ) / 13164 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13164 ≤ 2 * (370 / 100 : ℝ) / 13164 := by
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
    (completeRAData (tableEnvelope C) 13164 166).locationBound 13164 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13164 166).energyBound 13164 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13164 166) (d.f1 13164 166) d.f2 ≤
      32 * (((16365109 / 3906250000000000) : ℝ) + (1397677341 / 1000000000000000000) + (167966141 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13164 166) (d.w1 13164 166)
      (d.w2 13164 166) ≤
      32 * (((1646094539 / 100000000000000000000) : ℝ) + (1171164813 / 100000000000000000000) + (106978367 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13164 166) (d.f1 13164 166) d.f2 ≤
      ((16365109 / 3906250000000000) : ℝ) ^ 2 + 2 * ((16365109 / 3906250000000000)) * ((1397677341 / 1000000000000000000)) * (126 / 100) +
      2 * (((1397677341 / 1000000000000000000)) ^ 2 + 2 * ((16365109 / 3906250000000000)) * ((167966141 / 500000000000000000))) +
      6 * ((1397677341 / 1000000000000000000)) * ((167966141 / 500000000000000000)) * (126 / 100) + 8 * ((167966141 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13164 166) (d.f1 13164 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13164 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13164 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13164 166) (d.f1 13164 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13164 166) (d.w1 13164 166) (d.w2 13164 166)
  have hwexpr0 : 0 ≤ d.w0 13164 166 + d.w1 13164 166 * √(π / 2) +
      2 * d.w2 13164 166 + energyR16 13164 *
      radiusPolynomialRoot16 (d.w0 13164 166) (d.w1 13164 166) (d.w2 13164 166) := by
    positivity
  constructor
  · change (13164 : ℝ) ^ 8 * (mA 13164 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13164 166) (d.f1 13164 166) d.f2 + locationR16 13164 *
        radiusPolynomialRoot16 (d.f0 13164 166) (d.f1 13164 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13164 : ℝ) ^ 8 * (mA 13164 : ℝ) ^ 8 *
        ((((16365109 / 3906250000000000) : ℝ) ^ 2 + 2 * ((16365109 / 3906250000000000)) * ((1397677341 / 1000000000000000000)) * (126 / 100) +
          2 * (((1397677341 / 1000000000000000000)) ^ 2 + 2 * ((16365109 / 3906250000000000)) * ((167966141 / 500000000000000000))) +
          6 * ((1397677341 / 1000000000000000000)) * ((167966141 / 500000000000000000)) * (126 / 100) + 8 * ((167966141 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13164) *
          (32 * (((16365109 / 3906250000000000) : ℝ) + (1397677341 / 1000000000000000000) + (167966141 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13164 : ℝ) ^ 16 *
      (d.w0 13164 166 + d.w1 13164 166 * √(π / 2) + 2 * d.w2 13164 166 +
        energyR16 13164 * radiusPolynomialRoot16 (d.w0 13164 166) (d.w1 13164 166)
          (d.w2 13164 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13164 : ℝ) ^ 16 *
        (((1646094539 / 100000000000000000000) : ℝ) + ((1171164813 / 100000000000000000000)) * (126 / 100) + 2 * ((106978367 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13164) *
          (32 * (((1646094539 / 100000000000000000000) : ℝ) + (1171164813 / 100000000000000000000) + (106978367 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13164

/-! A coarse bound on the actual paper statistics constant at dimension 13165. -/
namespace BstLean.Part266.Row13165
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13163 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13163 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13163 128 ≤ (13417 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13417 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13165) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13165 : ℕ))
    (by norm_num : (13165 : ℕ) ≤ 16384)
  have ht : paperTail256 13165 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13165 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13165 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13165 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13165 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13165 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13163 128 * √(2 / (13165 : ℝ)) *
      (√(13165 : ℝ) + paperT0 13165 + paperTail256 13165) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13165 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13165 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13165 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13163 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13163 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13165 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13165

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13165
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13165 (61 / 100) 166 (17 / (100 * 13165)) (26 / (10 * 13165)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13165 (61 / 100) 166 (17 / (100 * 13165)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (106953061 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (649923661 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3832774097 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13165 / 13165 * (61 / 100)) ^ 4 * inverseRadius8 (13165 - 1) /
            envelopeGap 13165 (61 / 100) 166 (17 / (100 * 13165)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13165

namespace BstLean.Part266.Row13165
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13165 166 ≤ (4188670697 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13165 166 ≤ (349352887 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (83967111 / 250000000000000000)
  w0 : (tableEnvelope C).w0 13165 166 ≤ (1645719113 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13165 166 ≤ (1170897781 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13165 166 ≤ (427815957 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (106953061 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (106953061 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (649923661 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3832774097 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((359347 / 100000000) : ℝ) ≤ √(17 / (100 * 13165) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13165) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2068362261 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3605339543 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13165) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13165) ≤ (107422223 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13165) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13165 * (166 : ℝ) ^ 2 + 26 / (10 * 13165) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13165) : ℝ)) (tA 13165 * 166 ^ 2 + 26 / (10 * 13165)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((359347 / 100000000))) * ((106953061 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((359347 / 100000000)) ^ 3) * ((649923661 / 500000000000000000000000))) + ((3832774097 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((359347 / 100000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13165) : ℝ)) d.D d.V d.P (√(tA 13165) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((359347 / 100000000)) ^ 2 * (((2068362261 / 1000000000000000)) * ((3605339543 / 100000000000000000)))) + ((3832774097 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13165) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((359347 / 100000000)) * ((106953061 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13165) : ℝ)) (tA 13165 * 166 ^ 2 + 26 / (10 * 13165)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((106953061 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((359347 / 100000000)) ^ 2) * ((649923661 / 500000000000000000000000)) + ((3832774097 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13165) : ℝ)) (√(26 / (10 * 13165) : ℝ)) d.D d.V d.P (√(tA 13165) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((359347 / 100000000)) * (((2068362261 / 1000000000000000)) * ((3605339543 / 100000000000000000))) + ((3832774097 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13165) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((106953061 / 25000000000000000000) : ℝ) + ((3832774097 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13165

namespace BstLean.Part266.Row13165
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13165 166 ∧
    0 ≤ (tableEnvelope C).f1 13165 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13165 166 ∧
    0 ≤ (tableEnvelope C).w1 13165 166 ∧ 0 ≤ (tableEnvelope C).w2 13165 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13165 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13165 166 ∧ 0 ≤ d.f1 13165 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13165 166 ∧ 0 ≤ d.w1 13165 166 ∧ 0 ≤ d.w2 13165 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13165 ≤ 2 * (228 / 100 : ℝ) / 13165 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13165 ≤ 2 * (370 / 100 : ℝ) / 13165 := by
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
    (completeRAData (tableEnvelope C) 13165 166).locationBound 13165 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13165 166).energyBound 13165 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13165 166) (d.f1 13165 166) d.f2 ≤
      32 * (((4188670697 / 1000000000000000000) : ℝ) + (349352887 / 250000000000000000) + (83967111 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13165 166) (d.w1 13165 166)
      (d.w2 13165 166) ≤
      32 * (((1645719113 / 100000000000000000000) : ℝ) + (1170897781 / 100000000000000000000) + (427815957 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13165 166) (d.f1 13165 166) d.f2 ≤
      ((4188670697 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4188670697 / 1000000000000000000)) * ((349352887 / 250000000000000000)) * (126 / 100) +
      2 * (((349352887 / 250000000000000000)) ^ 2 + 2 * ((4188670697 / 1000000000000000000)) * ((83967111 / 250000000000000000))) +
      6 * ((349352887 / 250000000000000000)) * ((83967111 / 250000000000000000)) * (126 / 100) + 8 * ((83967111 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13165 166) (d.f1 13165 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13165 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13165 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13165 166) (d.f1 13165 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13165 166) (d.w1 13165 166) (d.w2 13165 166)
  have hwexpr0 : 0 ≤ d.w0 13165 166 + d.w1 13165 166 * √(π / 2) +
      2 * d.w2 13165 166 + energyR16 13165 *
      radiusPolynomialRoot16 (d.w0 13165 166) (d.w1 13165 166) (d.w2 13165 166) := by
    positivity
  constructor
  · change (13165 : ℝ) ^ 8 * (mA 13165 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13165 166) (d.f1 13165 166) d.f2 + locationR16 13165 *
        radiusPolynomialRoot16 (d.f0 13165 166) (d.f1 13165 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13165 : ℝ) ^ 8 * (mA 13165 : ℝ) ^ 8 *
        ((((4188670697 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4188670697 / 1000000000000000000)) * ((349352887 / 250000000000000000)) * (126 / 100) +
          2 * (((349352887 / 250000000000000000)) ^ 2 + 2 * ((4188670697 / 1000000000000000000)) * ((83967111 / 250000000000000000))) +
          6 * ((349352887 / 250000000000000000)) * ((83967111 / 250000000000000000)) * (126 / 100) + 8 * ((83967111 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13165) *
          (32 * (((4188670697 / 1000000000000000000) : ℝ) + (349352887 / 250000000000000000) + (83967111 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13165 : ℝ) ^ 16 *
      (d.w0 13165 166 + d.w1 13165 166 * √(π / 2) + 2 * d.w2 13165 166 +
        energyR16 13165 * radiusPolynomialRoot16 (d.w0 13165 166) (d.w1 13165 166)
          (d.w2 13165 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13165 : ℝ) ^ 16 *
        (((1645719113 / 100000000000000000000) : ℝ) + ((1170897781 / 100000000000000000000)) * (126 / 100) + 2 * ((427815957 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13165) *
          (32 * (((1645719113 / 100000000000000000000) : ℝ) + (1170897781 / 100000000000000000000) + (427815957 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13165

/-! A coarse bound on the actual paper statistics constant at dimension 13166. -/
namespace BstLean.Part266.Row13166
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13164 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13164 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13164 128 ≤ (13418 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13418 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13166) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13166 : ℕ))
    (by norm_num : (13166 : ℕ) ≤ 16384)
  have ht : paperTail256 13166 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13166 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13166 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13166 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13166 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13166 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13164 128 * √(2 / (13166 : ℝ)) *
      (√(13166 : ℝ) + paperT0 13166 + paperTail256 13166) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13166 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13166 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13166 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13164 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13164 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13166 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13166

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13166
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13166 (61 / 100) 166 (17 / (100 * 13166)) (26 / (10 * 13166)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13166 (61 / 100) 166 (17 / (100 * 13166)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (85542953 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1299452441 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3830423947 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13166 / 13166 * (61 / 100)) ^ 4 * inverseRadius8 (13166 - 1) /
            envelopeGap 13166 (61 / 100) 166 (17 / (100 * 13166)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13166

namespace BstLean.Part266.Row13166
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13166 166 ≤ (1046969279 / 250000000000000000)
  f1 : (tableEnvelope C).f1 13166 166 ≤ (1397146613 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (335804717 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13166 166 ≤ (1645344487 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13166 166 ≤ (585315579 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13166 166 ≤ (106929619 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (85542953 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (85542953 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1299452441 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3830423947 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3593333 / 1000000000) : ℝ) ≤ √(17 / (100 * 13166) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13166) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (517031651 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18023959339 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13166) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13166) ≤ (6713379 / 62500000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13166) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13166 * (166 : ℝ) ^ 2 + 26 / (10 * 13166) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13166) : ℝ)) (tA 13166 * 166 ^ 2 + 26 / (10 * 13166)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3593333 / 1000000000))) * ((85542953 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3593333 / 1000000000)) ^ 3) * ((1299452441 / 1000000000000000000000000))) + ((3830423947 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3593333 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13166) : ℝ)) d.D d.V d.P (√(tA 13166) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3593333 / 1000000000)) ^ 2 * (((517031651 / 250000000000000)) * ((18023959339 / 500000000000000000)))) + ((3830423947 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13166) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3593333 / 1000000000)) * ((85542953 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13166) : ℝ)) (tA 13166 * 166 ^ 2 + 26 / (10 * 13166)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((85542953 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3593333 / 1000000000)) ^ 2) * ((1299452441 / 1000000000000000000000000)) + ((3830423947 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13166) : ℝ)) (√(26 / (10 * 13166) : ℝ)) d.D d.V d.P (√(tA 13166) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3593333 / 1000000000)) * (((517031651 / 250000000000000)) * ((18023959339 / 500000000000000000))) + ((3830423947 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13166) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((85542953 / 20000000000000000000) : ℝ) + ((3830423947 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13166

namespace BstLean.Part266.Row13166
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13166 166 ∧
    0 ≤ (tableEnvelope C).f1 13166 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13166 166 ∧
    0 ≤ (tableEnvelope C).w1 13166 166 ∧ 0 ≤ (tableEnvelope C).w2 13166 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13166 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13166 166 ∧ 0 ≤ d.f1 13166 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13166 166 ∧ 0 ≤ d.w1 13166 166 ∧ 0 ≤ d.w2 13166 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13166 ≤ 2 * (228 / 100 : ℝ) / 13166 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13166 ≤ 2 * (370 / 100 : ℝ) / 13166 := by
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
    (completeRAData (tableEnvelope C) 13166 166).locationBound 13166 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13166 166).energyBound 13166 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13166 166) (d.f1 13166 166) d.f2 ≤
      32 * (((1046969279 / 250000000000000000) : ℝ) + (1397146613 / 1000000000000000000) + (335804717 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13166 166) (d.w1 13166 166)
      (d.w2 13166 166) ≤
      32 * (((1645344487 / 100000000000000000000) : ℝ) + (585315579 / 50000000000000000000) + (106929619 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13166 166) (d.f1 13166 166) d.f2 ≤
      ((1046969279 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1046969279 / 250000000000000000)) * ((1397146613 / 1000000000000000000)) * (126 / 100) +
      2 * (((1397146613 / 1000000000000000000)) ^ 2 + 2 * ((1046969279 / 250000000000000000)) * ((335804717 / 1000000000000000000))) +
      6 * ((1397146613 / 1000000000000000000)) * ((335804717 / 1000000000000000000)) * (126 / 100) + 8 * ((335804717 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13166 166) (d.f1 13166 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13166 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13166 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13166 166) (d.f1 13166 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13166 166) (d.w1 13166 166) (d.w2 13166 166)
  have hwexpr0 : 0 ≤ d.w0 13166 166 + d.w1 13166 166 * √(π / 2) +
      2 * d.w2 13166 166 + energyR16 13166 *
      radiusPolynomialRoot16 (d.w0 13166 166) (d.w1 13166 166) (d.w2 13166 166) := by
    positivity
  constructor
  · change (13166 : ℝ) ^ 8 * (mA 13166 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13166 166) (d.f1 13166 166) d.f2 + locationR16 13166 *
        radiusPolynomialRoot16 (d.f0 13166 166) (d.f1 13166 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13166 : ℝ) ^ 8 * (mA 13166 : ℝ) ^ 8 *
        ((((1046969279 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1046969279 / 250000000000000000)) * ((1397146613 / 1000000000000000000)) * (126 / 100) +
          2 * (((1397146613 / 1000000000000000000)) ^ 2 + 2 * ((1046969279 / 250000000000000000)) * ((335804717 / 1000000000000000000))) +
          6 * ((1397146613 / 1000000000000000000)) * ((335804717 / 1000000000000000000)) * (126 / 100) + 8 * ((335804717 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13166) *
          (32 * (((1046969279 / 250000000000000000) : ℝ) + (1397146613 / 1000000000000000000) + (335804717 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13166 : ℝ) ^ 16 *
      (d.w0 13166 166 + d.w1 13166 166 * √(π / 2) + 2 * d.w2 13166 166 +
        energyR16 13166 * radiusPolynomialRoot16 (d.w0 13166 166) (d.w1 13166 166)
          (d.w2 13166 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13166 : ℝ) ^ 16 *
        (((1645344487 / 100000000000000000000) : ℝ) + ((585315579 / 50000000000000000000)) * (126 / 100) + 2 * ((106929619 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13166) *
          (32 * (((1645344487 / 100000000000000000000) : ℝ) + (585315579 / 50000000000000000000) + (106929619 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13166

/-! A coarse bound on the actual paper statistics constant at dimension 13167. -/
namespace BstLean.Part266.Row13167
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13165 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13165 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13165 128 ≤ (13419 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13419 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13167) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13167 : ℕ))
    (by norm_num : (13167 : ℕ) ≤ 16384)
  have ht : paperTail256 13167 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13167 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13167 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13167 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13167 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13167 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13165 128 * √(2 / (13167 : ℝ)) *
      (√(13167 : ℝ) + paperT0 13167 + paperTail256 13167) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13167 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13167 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13167 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13165 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13165 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13167 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13167

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13167
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13167 (61 / 100) 166 (17 / (100 * 13167)) (26 / (10 * 13167)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13167 (61 / 100) 166 (17 / (100 * 13167)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (106904329 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1299057711 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3828075419 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13167 / 13167 * (61 / 100)) ^ 4 * inverseRadius8 (13167 - 1) /
            envelopeGap 13167 (61 / 100) 166 (17 / (100 * 13167)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13167

namespace BstLean.Part266.Row13167
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13167 166 ≤ (2093540219 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13167 166 ≤ (174610123 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (83935229 / 250000000000000000)
  w0 : (tableEnvelope C).w0 13167 166 ≤ (1644969309 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13167 166 ≤ (585182149 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13167 166 ≤ (17104841 / 4000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (106904329 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (106904329 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1299057711 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3828075419 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3593197 / 1000000000) : ℝ) ≤ √(17 / (100 * 13167) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13167) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1033945497 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36042443189 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13167) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13167) ≤ (53702953 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13167) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13167 * (166 : ℝ) ^ 2 + 26 / (10 * 13167) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13167) : ℝ)) (tA 13167 * 166 ^ 2 + 26 / (10 * 13167)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3593197 / 1000000000))) * ((106904329 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3593197 / 1000000000)) ^ 3) * ((1299057711 / 1000000000000000000000000))) + ((3828075419 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3593197 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13167) : ℝ)) d.D d.V d.P (√(tA 13167) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3593197 / 1000000000)) ^ 2 * (((1033945497 / 500000000000000)) * ((36042443189 / 1000000000000000000)))) + ((3828075419 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13167) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3593197 / 1000000000)) * ((106904329 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13167) : ℝ)) (tA 13167 * 166 ^ 2 + 26 / (10 * 13167)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((106904329 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3593197 / 1000000000)) ^ 2) * ((1299057711 / 1000000000000000000000000)) + ((3828075419 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13167) : ℝ)) (√(26 / (10 * 13167) : ℝ)) d.D d.V d.P (√(tA 13167) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3593197 / 1000000000)) * (((1033945497 / 500000000000000)) * ((36042443189 / 1000000000000000000))) + ((3828075419 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13167) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((106904329 / 25000000000000000000) : ℝ) + ((3828075419 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13167

namespace BstLean.Part266.Row13167
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13167 166 ∧
    0 ≤ (tableEnvelope C).f1 13167 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13167 166 ∧
    0 ≤ (tableEnvelope C).w1 13167 166 ∧ 0 ≤ (tableEnvelope C).w2 13167 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13167 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13167 166 ∧ 0 ≤ d.f1 13167 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13167 166 ∧ 0 ≤ d.w1 13167 166 ∧ 0 ≤ d.w2 13167 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13167 ≤ 2 * (228 / 100 : ℝ) / 13167 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13167 ≤ 2 * (370 / 100 : ℝ) / 13167 := by
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
    (completeRAData (tableEnvelope C) 13167 166).locationBound 13167 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13167 166).energyBound 13167 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13167 166) (d.f1 13167 166) d.f2 ≤
      32 * (((2093540219 / 500000000000000000) : ℝ) + (174610123 / 125000000000000000) + (83935229 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13167 166) (d.w1 13167 166)
      (d.w2 13167 166) ≤
      32 * (((1644969309 / 100000000000000000000) : ℝ) + (585182149 / 50000000000000000000) + (17104841 / 4000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13167 166) (d.f1 13167 166) d.f2 ≤
      ((2093540219 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2093540219 / 500000000000000000)) * ((174610123 / 125000000000000000)) * (126 / 100) +
      2 * (((174610123 / 125000000000000000)) ^ 2 + 2 * ((2093540219 / 500000000000000000)) * ((83935229 / 250000000000000000))) +
      6 * ((174610123 / 125000000000000000)) * ((83935229 / 250000000000000000)) * (126 / 100) + 8 * ((83935229 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13167 166) (d.f1 13167 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13167 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13167 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13167 166) (d.f1 13167 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13167 166) (d.w1 13167 166) (d.w2 13167 166)
  have hwexpr0 : 0 ≤ d.w0 13167 166 + d.w1 13167 166 * √(π / 2) +
      2 * d.w2 13167 166 + energyR16 13167 *
      radiusPolynomialRoot16 (d.w0 13167 166) (d.w1 13167 166) (d.w2 13167 166) := by
    positivity
  constructor
  · change (13167 : ℝ) ^ 8 * (mA 13167 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13167 166) (d.f1 13167 166) d.f2 + locationR16 13167 *
        radiusPolynomialRoot16 (d.f0 13167 166) (d.f1 13167 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13167 : ℝ) ^ 8 * (mA 13167 : ℝ) ^ 8 *
        ((((2093540219 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2093540219 / 500000000000000000)) * ((174610123 / 125000000000000000)) * (126 / 100) +
          2 * (((174610123 / 125000000000000000)) ^ 2 + 2 * ((2093540219 / 500000000000000000)) * ((83935229 / 250000000000000000))) +
          6 * ((174610123 / 125000000000000000)) * ((83935229 / 250000000000000000)) * (126 / 100) + 8 * ((83935229 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13167) *
          (32 * (((2093540219 / 500000000000000000) : ℝ) + (174610123 / 125000000000000000) + (83935229 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13167 : ℝ) ^ 16 *
      (d.w0 13167 166 + d.w1 13167 166 * √(π / 2) + 2 * d.w2 13167 166 +
        energyR16 13167 * radiusPolynomialRoot16 (d.w0 13167 166) (d.w1 13167 166)
          (d.w2 13167 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13167 : ℝ) ^ 16 *
        (((1644969309 / 100000000000000000000) : ℝ) + ((585182149 / 50000000000000000000)) * (126 / 100) + 2 * ((17104841 / 4000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13167) *
          (32 * (((1644969309 / 100000000000000000000) : ℝ) + (585182149 / 50000000000000000000) + (17104841 / 4000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13167

/-! A coarse bound on the actual paper statistics constant at dimension 13168. -/
namespace BstLean.Part266.Row13168
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13166 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13166 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13166 128 ≤ (13420 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13420 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13168) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13168 : ℕ))
    (by norm_num : (13168 : ℕ) ≤ 16384)
  have ht : paperTail256 13168 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13168 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13168 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13168 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13168 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13168 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13166 128 * √(2 / (13168 : ℝ)) *
      (√(13168 : ℝ) + paperT0 13168 + paperTail256 13168) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13168 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13168 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13168 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13166 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13166 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13168 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13168

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13168
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13168 (61 / 100) 166 (17 / (100 * 13168)) (26 / (10 * 13168)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13168 (61 / 100) 166 (17 / (100 * 13168)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (427519897 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (129866313 / 100000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3825728513 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13168 / 13168 * (61 / 100)) ^ 4 * inverseRadius8 (13168 - 1) /
            envelopeGap 13168 (61 / 100) 166 (17 / (100 * 13168)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13168

namespace BstLean.Part266.Row13168
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13168 166 ≤ (837257477 / 200000000000000000)
  f1 : (tableEnvelope C).f1 13168 166 ≤ (174577027 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (167838613 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13168 166 ≤ (1644594933 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13168 166 ≤ (1170097849 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13168 166 ≤ (427523603 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (427519897 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (427519897 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (129866313 / 100000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3825728513 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((179653 / 50000000) : ℝ) ≤ √(17 / (100 * 13168) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13168) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2067655429 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7207393787 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13168) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13168) ≤ (429591 / 4000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13168) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13168 * (166 : ℝ) ^ 2 + 26 / (10 * 13168) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13168) : ℝ)) (tA 13168 * 166 ^ 2 + 26 / (10 * 13168)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((179653 / 50000000))) * ((427519897 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((179653 / 50000000)) ^ 3) * ((129866313 / 100000000000000000000000))) + ((3825728513 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((179653 / 50000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13168) : ℝ)) d.D d.V d.P (√(tA 13168) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((179653 / 50000000)) ^ 2 * (((2067655429 / 1000000000000000)) * ((7207393787 / 200000000000000000)))) + ((3825728513 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13168) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((179653 / 50000000)) * ((427519897 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13168) : ℝ)) (tA 13168 * 166 ^ 2 + 26 / (10 * 13168)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((427519897 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((179653 / 50000000)) ^ 2) * ((129866313 / 100000000000000000000000)) + ((3825728513 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13168) : ℝ)) (√(26 / (10 * 13168) : ℝ)) d.D d.V d.P (√(tA 13168) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((179653 / 50000000)) * (((2067655429 / 1000000000000000)) * ((7207393787 / 200000000000000000))) + ((3825728513 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13168) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((427519897 / 100000000000000000000) : ℝ) + ((3825728513 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13168

namespace BstLean.Part266.Row13168
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13168 166 ∧
    0 ≤ (tableEnvelope C).f1 13168 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13168 166 ∧
    0 ≤ (tableEnvelope C).w1 13168 166 ∧ 0 ≤ (tableEnvelope C).w2 13168 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13168 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13168 166 ∧ 0 ≤ d.f1 13168 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13168 166 ∧ 0 ≤ d.w1 13168 166 ∧ 0 ≤ d.w2 13168 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13168 ≤ 2 * (228 / 100 : ℝ) / 13168 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13168 ≤ 2 * (370 / 100 : ℝ) / 13168 := by
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
    (completeRAData (tableEnvelope C) 13168 166).locationBound 13168 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13168 166).energyBound 13168 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13168 166) (d.f1 13168 166) d.f2 ≤
      32 * (((837257477 / 200000000000000000) : ℝ) + (174577027 / 125000000000000000) + (167838613 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13168 166) (d.w1 13168 166)
      (d.w2 13168 166) ≤
      32 * (((1644594933 / 100000000000000000000) : ℝ) + (1170097849 / 100000000000000000000) + (427523603 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13168 166) (d.f1 13168 166) d.f2 ≤
      ((837257477 / 200000000000000000) : ℝ) ^ 2 + 2 * ((837257477 / 200000000000000000)) * ((174577027 / 125000000000000000)) * (126 / 100) +
      2 * (((174577027 / 125000000000000000)) ^ 2 + 2 * ((837257477 / 200000000000000000)) * ((167838613 / 500000000000000000))) +
      6 * ((174577027 / 125000000000000000)) * ((167838613 / 500000000000000000)) * (126 / 100) + 8 * ((167838613 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13168 166) (d.f1 13168 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13168 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13168 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13168 166) (d.f1 13168 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13168 166) (d.w1 13168 166) (d.w2 13168 166)
  have hwexpr0 : 0 ≤ d.w0 13168 166 + d.w1 13168 166 * √(π / 2) +
      2 * d.w2 13168 166 + energyR16 13168 *
      radiusPolynomialRoot16 (d.w0 13168 166) (d.w1 13168 166) (d.w2 13168 166) := by
    positivity
  constructor
  · change (13168 : ℝ) ^ 8 * (mA 13168 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13168 166) (d.f1 13168 166) d.f2 + locationR16 13168 *
        radiusPolynomialRoot16 (d.f0 13168 166) (d.f1 13168 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13168 : ℝ) ^ 8 * (mA 13168 : ℝ) ^ 8 *
        ((((837257477 / 200000000000000000) : ℝ) ^ 2 + 2 * ((837257477 / 200000000000000000)) * ((174577027 / 125000000000000000)) * (126 / 100) +
          2 * (((174577027 / 125000000000000000)) ^ 2 + 2 * ((837257477 / 200000000000000000)) * ((167838613 / 500000000000000000))) +
          6 * ((174577027 / 125000000000000000)) * ((167838613 / 500000000000000000)) * (126 / 100) + 8 * ((167838613 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13168) *
          (32 * (((837257477 / 200000000000000000) : ℝ) + (174577027 / 125000000000000000) + (167838613 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13168 : ℝ) ^ 16 *
      (d.w0 13168 166 + d.w1 13168 166 * √(π / 2) + 2 * d.w2 13168 166 +
        energyR16 13168 * radiusPolynomialRoot16 (d.w0 13168 166) (d.w1 13168 166)
          (d.w2 13168 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13168 : ℝ) ^ 16 *
        (((1644594933 / 100000000000000000000) : ℝ) + ((1170097849 / 100000000000000000000)) * (126 / 100) + 2 * ((427523603 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13168) *
          (32 * (((1644594933 / 100000000000000000000) : ℝ) + (1170097849 / 100000000000000000000) + (427523603 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13168

/-! A coarse bound on the actual paper statistics constant at dimension 13169. -/
namespace BstLean.Part266.Row13169
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13167 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13167 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13167 128 ≤ (13421 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13421 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13169) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13169 : ℕ))
    (by norm_num : (13169 : ℕ) ≤ 16384)
  have ht : paperTail256 13169 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13169 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13169 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13169 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13169 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13169 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13167 128 * √(2 / (13169 : ℝ)) *
      (√(13169 : ℝ) + paperT0 13169 + paperTail256 13169) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13169 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13169 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13169 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13167 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13167 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13169 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13169

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13169
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13169 (61 / 100) 166 (17 / (100 * 13169)) (26 / (10 * 13169)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13169 (61 / 100) 166 (17 / (100 * 13169)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (427422507 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (12982687 / 10000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3823383227 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13169 / 13169 * (61 / 100)) ^ 4 * inverseRadius8 (13169 - 1) /
            envelopeGap 13169 (61 / 100) 166 (17 / (100 * 13169)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13169

namespace BstLean.Part266.Row13169
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13169 166 ≤ (837098247 / 200000000000000000)
  f1 : (tableEnvelope C).f1 13169 166 ≤ (43635961 / 31250000000000000)
  f2 : (tableEnvelope C).f2 ≤ (167806731 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13169 166 ≤ (411055001 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 13169 166 ≤ (29245779 / 2500000000000000000)
  w2 : (tableEnvelope C).w2 13169 166 ≤ (427426211 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (427422507 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (427422507 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (12982687 / 10000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3823383227 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((898231 / 250000000) : ℝ) ≤ √(17 / (100 * 13169) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13169) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2067419907 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7206299189 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13169) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13169) ≤ (53694797 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13169) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13169 * (166 : ℝ) ^ 2 + 26 / (10 * 13169) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13169) : ℝ)) (tA 13169 * 166 ^ 2 + 26 / (10 * 13169)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((898231 / 250000000))) * ((427422507 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((898231 / 250000000)) ^ 3) * ((12982687 / 10000000000000000000000))) + ((3823383227 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((898231 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13169) : ℝ)) d.D d.V d.P (√(tA 13169) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((898231 / 250000000)) ^ 2 * (((2067419907 / 1000000000000000)) * ((7206299189 / 200000000000000000)))) + ((3823383227 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13169) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((898231 / 250000000)) * ((427422507 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13169) : ℝ)) (tA 13169 * 166 ^ 2 + 26 / (10 * 13169)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((427422507 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((898231 / 250000000)) ^ 2) * ((12982687 / 10000000000000000000000)) + ((3823383227 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13169) : ℝ)) (√(26 / (10 * 13169) : ℝ)) d.D d.V d.P (√(tA 13169) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((898231 / 250000000)) * (((2067419907 / 1000000000000000)) * ((7206299189 / 200000000000000000))) + ((3823383227 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13169) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((427422507 / 100000000000000000000) : ℝ) + ((3823383227 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13169

namespace BstLean.Part266.Row13169
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13169 166 ∧
    0 ≤ (tableEnvelope C).f1 13169 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13169 166 ∧
    0 ≤ (tableEnvelope C).w1 13169 166 ∧ 0 ≤ (tableEnvelope C).w2 13169 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13169 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13169 166 ∧ 0 ≤ d.f1 13169 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13169 166 ∧ 0 ≤ d.w1 13169 166 ∧ 0 ≤ d.w2 13169 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13169 ≤ 2 * (228 / 100 : ℝ) / 13169 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13169 ≤ 2 * (370 / 100 : ℝ) / 13169 := by
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
    (completeRAData (tableEnvelope C) 13169 166).locationBound 13169 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13169 166).energyBound 13169 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13169 166) (d.f1 13169 166) d.f2 ≤
      32 * (((837098247 / 200000000000000000) : ℝ) + (43635961 / 31250000000000000) + (167806731 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13169 166) (d.w1 13169 166)
      (d.w2 13169 166) ≤
      32 * (((411055001 / 25000000000000000000) : ℝ) + (29245779 / 2500000000000000000) + (427426211 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13169 166) (d.f1 13169 166) d.f2 ≤
      ((837098247 / 200000000000000000) : ℝ) ^ 2 + 2 * ((837098247 / 200000000000000000)) * ((43635961 / 31250000000000000)) * (126 / 100) +
      2 * (((43635961 / 31250000000000000)) ^ 2 + 2 * ((837098247 / 200000000000000000)) * ((167806731 / 500000000000000000))) +
      6 * ((43635961 / 31250000000000000)) * ((167806731 / 500000000000000000)) * (126 / 100) + 8 * ((167806731 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13169 166) (d.f1 13169 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13169 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13169 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13169 166) (d.f1 13169 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13169 166) (d.w1 13169 166) (d.w2 13169 166)
  have hwexpr0 : 0 ≤ d.w0 13169 166 + d.w1 13169 166 * √(π / 2) +
      2 * d.w2 13169 166 + energyR16 13169 *
      radiusPolynomialRoot16 (d.w0 13169 166) (d.w1 13169 166) (d.w2 13169 166) := by
    positivity
  constructor
  · change (13169 : ℝ) ^ 8 * (mA 13169 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13169 166) (d.f1 13169 166) d.f2 + locationR16 13169 *
        radiusPolynomialRoot16 (d.f0 13169 166) (d.f1 13169 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13169 : ℝ) ^ 8 * (mA 13169 : ℝ) ^ 8 *
        ((((837098247 / 200000000000000000) : ℝ) ^ 2 + 2 * ((837098247 / 200000000000000000)) * ((43635961 / 31250000000000000)) * (126 / 100) +
          2 * (((43635961 / 31250000000000000)) ^ 2 + 2 * ((837098247 / 200000000000000000)) * ((167806731 / 500000000000000000))) +
          6 * ((43635961 / 31250000000000000)) * ((167806731 / 500000000000000000)) * (126 / 100) + 8 * ((167806731 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13169) *
          (32 * (((837098247 / 200000000000000000) : ℝ) + (43635961 / 31250000000000000) + (167806731 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13169 : ℝ) ^ 16 *
      (d.w0 13169 166 + d.w1 13169 166 * √(π / 2) + 2 * d.w2 13169 166 +
        energyR16 13169 * radiusPolynomialRoot16 (d.w0 13169 166) (d.w1 13169 166)
          (d.w2 13169 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13169 : ℝ) ^ 16 *
        (((411055001 / 25000000000000000000) : ℝ) + ((29245779 / 2500000000000000000)) * (126 / 100) + 2 * ((427426211 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13169) *
          (32 * (((411055001 / 25000000000000000000) : ℝ) + (29245779 / 2500000000000000000) + (427426211 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13169

/-! A coarse bound on the actual paper statistics constant at dimension 13170. -/
namespace BstLean.Part266.Row13170
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13168 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13168 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13168 128 ≤ (13422 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13422 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13170) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13170 : ℕ))
    (by norm_num : (13170 : ℕ) ≤ 16384)
  have ht : paperTail256 13170 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13170 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13170 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13170 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13170 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13170 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13168 128 * √(2 / (13170 : ℝ)) *
      (√(13170 : ℝ) + paperT0 13170 + paperTail256 13170) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13170 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13170 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13170 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13168 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13168 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13170 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13170

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13170
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13170 (61 / 100) 166 (17 / (100 * 13170)) (26 / (10 * 13170)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13170 (61 / 100) 166 (17 / (100 * 13170)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (427325147 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1297874419 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (95525989 / 25000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13170 / 13170 * (61 / 100)) ^ 4 * inverseRadius8 (13170 - 1) /
            envelopeGap 13170 (61 / 100) 166 (17 / (100 * 13170)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13170

namespace BstLean.Part266.Row13170
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13170 166 ≤ (4184698709 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13170 166 ≤ (349021537 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (335549809 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13170 166 ≤ (1643845877 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13170 166 ≤ (292391221 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 13170 166 ≤ (427328849 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (427325147 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (427325147 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1297874419 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (95525989 / 25000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3592787 / 1000000000) : ℝ) ≤ √(17 / (100 * 13170) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13170) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2067184431 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36026024191 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13170) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13170) ≤ (335567 / 3125000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13170) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13170 * (166 : ℝ) ^ 2 + 26 / (10 * 13170) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13170) : ℝ)) (tA 13170 * 166 ^ 2 + 26 / (10 * 13170)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3592787 / 1000000000))) * ((427325147 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3592787 / 1000000000)) ^ 3) * ((1297874419 / 1000000000000000000000000))) + ((95525989 / 25000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3592787 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13170) : ℝ)) d.D d.V d.P (√(tA 13170) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3592787 / 1000000000)) ^ 2 * (((2067184431 / 1000000000000000)) * ((36026024191 / 1000000000000000000)))) + ((95525989 / 25000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13170) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3592787 / 1000000000)) * ((427325147 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13170) : ℝ)) (tA 13170 * 166 ^ 2 + 26 / (10 * 13170)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((427325147 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3592787 / 1000000000)) ^ 2) * ((1297874419 / 1000000000000000000000000)) + ((95525989 / 25000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13170) : ℝ)) (√(26 / (10 * 13170) : ℝ)) d.D d.V d.P (√(tA 13170) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3592787 / 1000000000)) * (((2067184431 / 1000000000000000)) * ((36026024191 / 1000000000000000000))) + ((95525989 / 25000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13170) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((427325147 / 100000000000000000000) : ℝ) + ((95525989 / 25000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13170

namespace BstLean.Part266.Row13170
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13170 166 ∧
    0 ≤ (tableEnvelope C).f1 13170 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13170 166 ∧
    0 ≤ (tableEnvelope C).w1 13170 166 ∧ 0 ≤ (tableEnvelope C).w2 13170 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13170 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13170 166 ∧ 0 ≤ d.f1 13170 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13170 166 ∧ 0 ≤ d.w1 13170 166 ∧ 0 ≤ d.w2 13170 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13170 ≤ 2 * (228 / 100 : ℝ) / 13170 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13170 ≤ 2 * (370 / 100 : ℝ) / 13170 := by
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
    (completeRAData (tableEnvelope C) 13170 166).locationBound 13170 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13170 166).energyBound 13170 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13170 166) (d.f1 13170 166) d.f2 ≤
      32 * (((4184698709 / 1000000000000000000) : ℝ) + (349021537 / 250000000000000000) + (335549809 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13170 166) (d.w1 13170 166)
      (d.w2 13170 166) ≤
      32 * (((1643845877 / 100000000000000000000) : ℝ) + (292391221 / 25000000000000000000) + (427328849 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13170 166) (d.f1 13170 166) d.f2 ≤
      ((4184698709 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4184698709 / 1000000000000000000)) * ((349021537 / 250000000000000000)) * (126 / 100) +
      2 * (((349021537 / 250000000000000000)) ^ 2 + 2 * ((4184698709 / 1000000000000000000)) * ((335549809 / 1000000000000000000))) +
      6 * ((349021537 / 250000000000000000)) * ((335549809 / 1000000000000000000)) * (126 / 100) + 8 * ((335549809 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13170 166) (d.f1 13170 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13170 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13170 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13170 166) (d.f1 13170 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13170 166) (d.w1 13170 166) (d.w2 13170 166)
  have hwexpr0 : 0 ≤ d.w0 13170 166 + d.w1 13170 166 * √(π / 2) +
      2 * d.w2 13170 166 + energyR16 13170 *
      radiusPolynomialRoot16 (d.w0 13170 166) (d.w1 13170 166) (d.w2 13170 166) := by
    positivity
  constructor
  · change (13170 : ℝ) ^ 8 * (mA 13170 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13170 166) (d.f1 13170 166) d.f2 + locationR16 13170 *
        radiusPolynomialRoot16 (d.f0 13170 166) (d.f1 13170 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13170 : ℝ) ^ 8 * (mA 13170 : ℝ) ^ 8 *
        ((((4184698709 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4184698709 / 1000000000000000000)) * ((349021537 / 250000000000000000)) * (126 / 100) +
          2 * (((349021537 / 250000000000000000)) ^ 2 + 2 * ((4184698709 / 1000000000000000000)) * ((335549809 / 1000000000000000000))) +
          6 * ((349021537 / 250000000000000000)) * ((335549809 / 1000000000000000000)) * (126 / 100) + 8 * ((335549809 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13170) *
          (32 * (((4184698709 / 1000000000000000000) : ℝ) + (349021537 / 250000000000000000) + (335549809 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13170 : ℝ) ^ 16 *
      (d.w0 13170 166 + d.w1 13170 166 * √(π / 2) + 2 * d.w2 13170 166 +
        energyR16 13170 * radiusPolynomialRoot16 (d.w0 13170 166) (d.w1 13170 166)
          (d.w2 13170 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13170 : ℝ) ^ 16 *
        (((1643845877 / 100000000000000000000) : ℝ) + ((292391221 / 25000000000000000000)) * (126 / 100) + 2 * ((427328849 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13170) *
          (32 * (((1643845877 / 100000000000000000000) : ℝ) + (292391221 / 25000000000000000000) + (427328849 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13170

/-! A coarse bound on the actual paper statistics constant at dimension 13171. -/
namespace BstLean.Part266.Row13171
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13169 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13169 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13169 128 ≤ (13423 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13423 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13171) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13171 : ℕ))
    (by norm_num : (13171 : ℕ) ≤ 16384)
  have ht : paperTail256 13171 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13171 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13171 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13171 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13171 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13171 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13169 128 * √(2 / (13171 : ℝ)) *
      (√(13171 : ℝ) + paperT0 13171 + paperTail256 13171) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13171 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13171 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13171 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13169 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13169 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13171 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13171

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13171
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13171 (61 / 100) 166 (17 / (100 * 13171)) (26 / (10 * 13171)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13171 (61 / 100) 166 (17 / (100 * 13171)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (53403477 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1297480287 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (381869751 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13171 / 13171 * (61 / 100)) ^ 4 * inverseRadius8 (13171 - 1) /
            envelopeGap 13171 (61 / 100) 166 (17 / (100 * 13171)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13171

namespace BstLean.Part266.Row13171
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13171 166 ≤ (2091951541 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13171 166 ≤ (1395820849 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (335486081 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13171 166 ≤ (328694239 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 13171 166 ≤ (584649183 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13171 166 ≤ (106807879 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (53403477 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (53403477 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1297480287 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (381869751 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3592651 / 1000000000) : ℝ) ≤ √(17 / (100 * 13171) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13171) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1033474499 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1440822147 / 40000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13171) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13171) ≤ (107373287 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13171) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13171 * (166 : ℝ) ^ 2 + 26 / (10 * 13171) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13171) : ℝ)) (tA 13171 * 166 ^ 2 + 26 / (10 * 13171)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3592651 / 1000000000))) * ((53403477 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3592651 / 1000000000)) ^ 3) * ((1297480287 / 1000000000000000000000000))) + ((381869751 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3592651 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13171) : ℝ)) d.D d.V d.P (√(tA 13171) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3592651 / 1000000000)) ^ 2 * (((1033474499 / 500000000000000)) * ((1440822147 / 40000000000000000)))) + ((381869751 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13171) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3592651 / 1000000000)) * ((53403477 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13171) : ℝ)) (tA 13171 * 166 ^ 2 + 26 / (10 * 13171)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((53403477 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3592651 / 1000000000)) ^ 2) * ((1297480287 / 1000000000000000000000000)) + ((381869751 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13171) : ℝ)) (√(26 / (10 * 13171) : ℝ)) d.D d.V d.P (√(tA 13171) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3592651 / 1000000000)) * (((1033474499 / 500000000000000)) * ((1440822147 / 40000000000000000))) + ((381869751 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13171) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((53403477 / 12500000000000000000) : ℝ) + ((381869751 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13171

namespace BstLean.Part266.Row13171
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13171 166 ∧
    0 ≤ (tableEnvelope C).f1 13171 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13171 166 ∧
    0 ≤ (tableEnvelope C).w1 13171 166 ∧ 0 ≤ (tableEnvelope C).w2 13171 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13171 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13171 166 ∧ 0 ≤ d.f1 13171 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13171 166 ∧ 0 ≤ d.w1 13171 166 ∧ 0 ≤ d.w2 13171 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13171 ≤ 2 * (228 / 100 : ℝ) / 13171 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13171 ≤ 2 * (370 / 100 : ℝ) / 13171 := by
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
    (completeRAData (tableEnvelope C) 13171 166).locationBound 13171 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13171 166).energyBound 13171 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13171 166) (d.f1 13171 166) d.f2 ≤
      32 * (((2091951541 / 500000000000000000) : ℝ) + (1395820849 / 1000000000000000000) + (335486081 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13171 166) (d.w1 13171 166)
      (d.w2 13171 166) ≤
      32 * (((328694239 / 20000000000000000000) : ℝ) + (584649183 / 50000000000000000000) + (106807879 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13171 166) (d.f1 13171 166) d.f2 ≤
      ((2091951541 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2091951541 / 500000000000000000)) * ((1395820849 / 1000000000000000000)) * (126 / 100) +
      2 * (((1395820849 / 1000000000000000000)) ^ 2 + 2 * ((2091951541 / 500000000000000000)) * ((335486081 / 1000000000000000000))) +
      6 * ((1395820849 / 1000000000000000000)) * ((335486081 / 1000000000000000000)) * (126 / 100) + 8 * ((335486081 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13171 166) (d.f1 13171 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13171 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13171 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13171 166) (d.f1 13171 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13171 166) (d.w1 13171 166) (d.w2 13171 166)
  have hwexpr0 : 0 ≤ d.w0 13171 166 + d.w1 13171 166 * √(π / 2) +
      2 * d.w2 13171 166 + energyR16 13171 *
      radiusPolynomialRoot16 (d.w0 13171 166) (d.w1 13171 166) (d.w2 13171 166) := by
    positivity
  constructor
  · change (13171 : ℝ) ^ 8 * (mA 13171 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13171 166) (d.f1 13171 166) d.f2 + locationR16 13171 *
        radiusPolynomialRoot16 (d.f0 13171 166) (d.f1 13171 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13171 : ℝ) ^ 8 * (mA 13171 : ℝ) ^ 8 *
        ((((2091951541 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2091951541 / 500000000000000000)) * ((1395820849 / 1000000000000000000)) * (126 / 100) +
          2 * (((1395820849 / 1000000000000000000)) ^ 2 + 2 * ((2091951541 / 500000000000000000)) * ((335486081 / 1000000000000000000))) +
          6 * ((1395820849 / 1000000000000000000)) * ((335486081 / 1000000000000000000)) * (126 / 100) + 8 * ((335486081 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13171) *
          (32 * (((2091951541 / 500000000000000000) : ℝ) + (1395820849 / 1000000000000000000) + (335486081 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13171 : ℝ) ^ 16 *
      (d.w0 13171 166 + d.w1 13171 166 * √(π / 2) + 2 * d.w2 13171 166 +
        energyR16 13171 * radiusPolynomialRoot16 (d.w0 13171 166) (d.w1 13171 166)
          (d.w2 13171 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13171 : ℝ) ^ 16 *
        (((328694239 / 20000000000000000000) : ℝ) + ((584649183 / 50000000000000000000)) * (126 / 100) + 2 * ((106807879 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13171) *
          (32 * (((328694239 / 20000000000000000000) : ℝ) + (584649183 / 50000000000000000000) + (106807879 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13171

/-! A coarse bound on the actual paper statistics constant at dimension 13172. -/
namespace BstLean.Part266.Row13172
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13170 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13170 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13170 128 ≤ (13424 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13424 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13172) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13172 : ℕ))
    (by norm_num : (13172 : ℕ) ≤ 16384)
  have ht : paperTail256 13172 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13172 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13172 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13172 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13172 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13172 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13170 128 * √(2 / (13172 : ℝ)) *
      (√(13172 : ℝ) + paperT0 13172 + paperTail256 13172) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13172 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13172 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13172 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13170 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13170 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13172 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13172

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13172
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13172 (61 / 100) 166 (17 / (100 * 13172)) (26 / (10 * 13172)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13172 (61 / 100) 166 (17 / (100 * 13172)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (85426103 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (648543153 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3816357077 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13172 / 13172 * (61 / 100)) ^ 4 * inverseRadius8 (13172 - 1) /
            envelopeGap 13172 (61 / 100) 166 (17 / (100 * 13172)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13172

namespace BstLean.Part266.Row13172
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13172 166 ≤ (4183107723 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13172 166 ≤ (697777817 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (335422371 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13172 166 ≤ (5134677 / 312500000000000000)
  w1 : (tableEnvelope C).w1 13172 166 ≤ (4566531 / 390625000000000000)
  w2 : (tableEnvelope C).w2 13172 166 ≤ (106783553 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (85426103 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (85426103 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (648543153 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3816357077 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((718503 / 200000000) : ℝ) ≤ √(17 / (100 * 13172) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13172) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (516678403 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4501885553 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13172) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13172) ≤ (6710321 / 62500000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13172) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13172 * (166 : ℝ) ^ 2 + 26 / (10 * 13172) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13172) : ℝ)) (tA 13172 * 166 ^ 2 + 26 / (10 * 13172)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((718503 / 200000000))) * ((85426103 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((718503 / 200000000)) ^ 3) * ((648543153 / 500000000000000000000000))) + ((3816357077 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((718503 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13172) : ℝ)) d.D d.V d.P (√(tA 13172) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((718503 / 200000000)) ^ 2 * (((516678403 / 250000000000000)) * ((4501885553 / 125000000000000000)))) + ((3816357077 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13172) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((718503 / 200000000)) * ((85426103 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13172) : ℝ)) (tA 13172 * 166 ^ 2 + 26 / (10 * 13172)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((85426103 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((718503 / 200000000)) ^ 2) * ((648543153 / 500000000000000000000000)) + ((3816357077 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13172) : ℝ)) (√(26 / (10 * 13172) : ℝ)) d.D d.V d.P (√(tA 13172) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((718503 / 200000000)) * (((516678403 / 250000000000000)) * ((4501885553 / 125000000000000000))) + ((3816357077 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13172) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((85426103 / 20000000000000000000) : ℝ) + ((3816357077 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13172

namespace BstLean.Part266.Row13172
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13172 166 ∧
    0 ≤ (tableEnvelope C).f1 13172 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13172 166 ∧
    0 ≤ (tableEnvelope C).w1 13172 166 ∧ 0 ≤ (tableEnvelope C).w2 13172 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13172 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13172 166 ∧ 0 ≤ d.f1 13172 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13172 166 ∧ 0 ≤ d.w1 13172 166 ∧ 0 ≤ d.w2 13172 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13172 ≤ 2 * (228 / 100 : ℝ) / 13172 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13172 ≤ 2 * (370 / 100 : ℝ) / 13172 := by
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
    (completeRAData (tableEnvelope C) 13172 166).locationBound 13172 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13172 166).energyBound 13172 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13172 166) (d.f1 13172 166) d.f2 ≤
      32 * (((4183107723 / 1000000000000000000) : ℝ) + (697777817 / 500000000000000000) + (335422371 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13172 166) (d.w1 13172 166)
      (d.w2 13172 166) ≤
      32 * (((5134677 / 312500000000000000) : ℝ) + (4566531 / 390625000000000000) + (106783553 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13172 166) (d.f1 13172 166) d.f2 ≤
      ((4183107723 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4183107723 / 1000000000000000000)) * ((697777817 / 500000000000000000)) * (126 / 100) +
      2 * (((697777817 / 500000000000000000)) ^ 2 + 2 * ((4183107723 / 1000000000000000000)) * ((335422371 / 1000000000000000000))) +
      6 * ((697777817 / 500000000000000000)) * ((335422371 / 1000000000000000000)) * (126 / 100) + 8 * ((335422371 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13172 166) (d.f1 13172 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13172 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13172 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13172 166) (d.f1 13172 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13172 166) (d.w1 13172 166) (d.w2 13172 166)
  have hwexpr0 : 0 ≤ d.w0 13172 166 + d.w1 13172 166 * √(π / 2) +
      2 * d.w2 13172 166 + energyR16 13172 *
      radiusPolynomialRoot16 (d.w0 13172 166) (d.w1 13172 166) (d.w2 13172 166) := by
    positivity
  constructor
  · change (13172 : ℝ) ^ 8 * (mA 13172 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13172 166) (d.f1 13172 166) d.f2 + locationR16 13172 *
        radiusPolynomialRoot16 (d.f0 13172 166) (d.f1 13172 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13172 : ℝ) ^ 8 * (mA 13172 : ℝ) ^ 8 *
        ((((4183107723 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4183107723 / 1000000000000000000)) * ((697777817 / 500000000000000000)) * (126 / 100) +
          2 * (((697777817 / 500000000000000000)) ^ 2 + 2 * ((4183107723 / 1000000000000000000)) * ((335422371 / 1000000000000000000))) +
          6 * ((697777817 / 500000000000000000)) * ((335422371 / 1000000000000000000)) * (126 / 100) + 8 * ((335422371 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13172) *
          (32 * (((4183107723 / 1000000000000000000) : ℝ) + (697777817 / 500000000000000000) + (335422371 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13172 : ℝ) ^ 16 *
      (d.w0 13172 166 + d.w1 13172 166 * √(π / 2) + 2 * d.w2 13172 166 +
        energyR16 13172 * radiusPolynomialRoot16 (d.w0 13172 166) (d.w1 13172 166)
          (d.w2 13172 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13172 : ℝ) ^ 16 *
        (((5134677 / 312500000000000000) : ℝ) + ((4566531 / 390625000000000000)) * (126 / 100) + 2 * ((106783553 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13172) *
          (32 * (((5134677 / 312500000000000000) : ℝ) + (4566531 / 390625000000000000) + (106783553 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13172

/-! A coarse bound on the actual paper statistics constant at dimension 13173. -/
namespace BstLean.Part266.Row13173
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13171 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13171 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13171 128 ≤ (13425 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13425 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13173) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13173 : ℕ))
    (by norm_num : (13173 : ℕ) ≤ 16384)
  have ht : paperTail256 13173 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13173 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13173 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13173 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13173 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13173 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13171 128 * √(2 / (13173 : ℝ)) *
      (√(13173 : ℝ) + paperT0 13173 + paperTail256 13173) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13173 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13173 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13173 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13171 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13171 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13173 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13173

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13173
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13173 (61 / 100) 166 (17 / (100 * 13173)) (26 / (10 * 13173)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13173 (61 / 100) 166 (17 / (100 * 13173)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (427033243 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (648346237 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (190700913 / 50000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13173 / 13173 * (61 / 100)) ^ 4 * inverseRadius8 (13173 - 1) /
            envelopeGap 13173 (61 / 100) 166 (17 / (100 * 13173)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13173

namespace BstLean.Part266.Row13173
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13173 166 ≤ (4182315987 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13173 166 ≤ (348822819 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (335358773 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13173 166 ≤ (410680721 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 13173 166 ≤ (292191479 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 13173 166 ≤ (213518469 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (427033243 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (427033243 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (648346237 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (190700913 / 50000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1796189 / 500000000) : ℝ) ≤ √(17 / (100 * 13173) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13173) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (516619567 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36009616411 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13173) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13173) ≤ (21471397 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13173) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13173 * (166 : ℝ) ^ 2 + 26 / (10 * 13173) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13173) : ℝ)) (tA 13173 * 166 ^ 2 + 26 / (10 * 13173)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1796189 / 500000000))) * ((427033243 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1796189 / 500000000)) ^ 3) * ((648346237 / 500000000000000000000000))) + ((190700913 / 50000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1796189 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13173) : ℝ)) d.D d.V d.P (√(tA 13173) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1796189 / 500000000)) ^ 2 * (((516619567 / 250000000000000)) * ((36009616411 / 1000000000000000000)))) + ((190700913 / 50000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13173) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1796189 / 500000000)) * ((427033243 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13173) : ℝ)) (tA 13173 * 166 ^ 2 + 26 / (10 * 13173)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((427033243 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1796189 / 500000000)) ^ 2) * ((648346237 / 500000000000000000000000)) + ((190700913 / 50000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13173) : ℝ)) (√(26 / (10 * 13173) : ℝ)) d.D d.V d.P (√(tA 13173) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1796189 / 500000000)) * (((516619567 / 250000000000000)) * ((36009616411 / 1000000000000000000))) + ((190700913 / 50000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13173) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((427033243 / 100000000000000000000) : ℝ) + ((190700913 / 50000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13173

namespace BstLean.Part266.Row13173
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13173 166 ∧
    0 ≤ (tableEnvelope C).f1 13173 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13173 166 ∧
    0 ≤ (tableEnvelope C).w1 13173 166 ∧ 0 ≤ (tableEnvelope C).w2 13173 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13173 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13173 166 ∧ 0 ≤ d.f1 13173 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13173 166 ∧ 0 ≤ d.w1 13173 166 ∧ 0 ≤ d.w2 13173 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13173 ≤ 2 * (228 / 100 : ℝ) / 13173 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13173 ≤ 2 * (370 / 100 : ℝ) / 13173 := by
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
    (completeRAData (tableEnvelope C) 13173 166).locationBound 13173 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13173 166).energyBound 13173 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13173 166) (d.f1 13173 166) d.f2 ≤
      32 * (((4182315987 / 1000000000000000000) : ℝ) + (348822819 / 250000000000000000) + (335358773 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13173 166) (d.w1 13173 166)
      (d.w2 13173 166) ≤
      32 * (((410680721 / 25000000000000000000) : ℝ) + (292191479 / 25000000000000000000) + (213518469 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13173 166) (d.f1 13173 166) d.f2 ≤
      ((4182315987 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4182315987 / 1000000000000000000)) * ((348822819 / 250000000000000000)) * (126 / 100) +
      2 * (((348822819 / 250000000000000000)) ^ 2 + 2 * ((4182315987 / 1000000000000000000)) * ((335358773 / 1000000000000000000))) +
      6 * ((348822819 / 250000000000000000)) * ((335358773 / 1000000000000000000)) * (126 / 100) + 8 * ((335358773 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13173 166) (d.f1 13173 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13173 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13173 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13173 166) (d.f1 13173 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13173 166) (d.w1 13173 166) (d.w2 13173 166)
  have hwexpr0 : 0 ≤ d.w0 13173 166 + d.w1 13173 166 * √(π / 2) +
      2 * d.w2 13173 166 + energyR16 13173 *
      radiusPolynomialRoot16 (d.w0 13173 166) (d.w1 13173 166) (d.w2 13173 166) := by
    positivity
  constructor
  · change (13173 : ℝ) ^ 8 * (mA 13173 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13173 166) (d.f1 13173 166) d.f2 + locationR16 13173 *
        radiusPolynomialRoot16 (d.f0 13173 166) (d.f1 13173 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13173 : ℝ) ^ 8 * (mA 13173 : ℝ) ^ 8 *
        ((((4182315987 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4182315987 / 1000000000000000000)) * ((348822819 / 250000000000000000)) * (126 / 100) +
          2 * (((348822819 / 250000000000000000)) ^ 2 + 2 * ((4182315987 / 1000000000000000000)) * ((335358773 / 1000000000000000000))) +
          6 * ((348822819 / 250000000000000000)) * ((335358773 / 1000000000000000000)) * (126 / 100) + 8 * ((335358773 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13173) *
          (32 * (((4182315987 / 1000000000000000000) : ℝ) + (348822819 / 250000000000000000) + (335358773 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13173 : ℝ) ^ 16 *
      (d.w0 13173 166 + d.w1 13173 166 * √(π / 2) + 2 * d.w2 13173 166 +
        energyR16 13173 * radiusPolynomialRoot16 (d.w0 13173 166) (d.w1 13173 166)
          (d.w2 13173 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13173 : ℝ) ^ 16 *
        (((410680721 / 25000000000000000000) : ℝ) + ((292191479 / 25000000000000000000)) * (126 / 100) + 2 * ((213518469 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13173) *
          (32 * (((410680721 / 25000000000000000000) : ℝ) + (292191479 / 25000000000000000000) + (213518469 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13173

/-! A coarse bound on the actual paper statistics constant at dimension 13174. -/
namespace BstLean.Part266.Row13174
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13172 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13172 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13172 128 ≤ (13426 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13426 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13174) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13174 : ℕ))
    (by norm_num : (13174 : ℕ) ≤ 16384)
  have ht : paperTail256 13174 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13174 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13174 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13174 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13174 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13174 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13172 128 * √(2 / (13174 : ℝ)) *
      (√(13174 : ℝ) + paperT0 13174 + paperTail256 13174) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13174 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13174 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13174 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13172 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13172 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13174 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13174

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13174
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13174 (61 / 100) 166 (17 / (100 * 13174)) (26 / (10 * 13174)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13174 (61 / 100) 166 (17 / (100 * 13174)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (426936001 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1296298791 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (119115033 / 31250000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13174 / 13174 * (61 / 100)) ^ 4 * inverseRadius8 (13174 - 1) /
            envelopeGap 13174 (61 / 100) 166 (17 / (100 * 13174)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13174

namespace BstLean.Part266.Row13174
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13174 166 ≤ (16334067 / 3906250000000000)
  f1 : (tableEnvelope C).f1 13174 166 ≤ (55801049 / 40000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (3352951 / 10000000000000000)
  w0 : (tableEnvelope C).w0 13174 166 ≤ (51323393 / 3125000000000000000)
  w1 : (tableEnvelope C).w1 13174 166 ≤ (1168499657 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13174 166 ≤ (213469847 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (426936001 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (426936001 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1296298791 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (119115033 / 31250000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1796121 / 500000000) : ℝ) ≤ √(17 / (100 * 13174) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13174) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (206624297 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9001037409 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13174) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13174) ≤ (26837209 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13174) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13174 * (166 : ℝ) ^ 2 + 26 / (10 * 13174) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13174) : ℝ)) (tA 13174 * 166 ^ 2 + 26 / (10 * 13174)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1796121 / 500000000))) * ((426936001 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1796121 / 500000000)) ^ 3) * ((1296298791 / 1000000000000000000000000))) + ((119115033 / 31250000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1796121 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13174) : ℝ)) d.D d.V d.P (√(tA 13174) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1796121 / 500000000)) ^ 2 * (((206624297 / 100000000000000)) * ((9001037409 / 250000000000000000)))) + ((119115033 / 31250000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13174) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1796121 / 500000000)) * ((426936001 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13174) : ℝ)) (tA 13174 * 166 ^ 2 + 26 / (10 * 13174)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((426936001 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1796121 / 500000000)) ^ 2) * ((1296298791 / 1000000000000000000000000)) + ((119115033 / 31250000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13174) : ℝ)) (√(26 / (10 * 13174) : ℝ)) d.D d.V d.P (√(tA 13174) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1796121 / 500000000)) * (((206624297 / 100000000000000)) * ((9001037409 / 250000000000000000))) + ((119115033 / 31250000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13174) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((426936001 / 100000000000000000000) : ℝ) + ((119115033 / 31250000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13174

namespace BstLean.Part266.Row13174
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13174 166 ∧
    0 ≤ (tableEnvelope C).f1 13174 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13174 166 ∧
    0 ≤ (tableEnvelope C).w1 13174 166 ∧ 0 ≤ (tableEnvelope C).w2 13174 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13174 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13174 166 ∧ 0 ≤ d.f1 13174 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13174 166 ∧ 0 ≤ d.w1 13174 166 ∧ 0 ≤ d.w2 13174 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13174 ≤ 2 * (228 / 100 : ℝ) / 13174 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13174 ≤ 2 * (370 / 100 : ℝ) / 13174 := by
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
    (completeRAData (tableEnvelope C) 13174 166).locationBound 13174 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13174 166).energyBound 13174 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13174 166) (d.f1 13174 166) d.f2 ≤
      32 * (((16334067 / 3906250000000000) : ℝ) + (55801049 / 40000000000000000) + (3352951 / 10000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13174 166) (d.w1 13174 166)
      (d.w2 13174 166) ≤
      32 * (((51323393 / 3125000000000000000) : ℝ) + (1168499657 / 100000000000000000000) + (213469847 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13174 166) (d.f1 13174 166) d.f2 ≤
      ((16334067 / 3906250000000000) : ℝ) ^ 2 + 2 * ((16334067 / 3906250000000000)) * ((55801049 / 40000000000000000)) * (126 / 100) +
      2 * (((55801049 / 40000000000000000)) ^ 2 + 2 * ((16334067 / 3906250000000000)) * ((3352951 / 10000000000000000))) +
      6 * ((55801049 / 40000000000000000)) * ((3352951 / 10000000000000000)) * (126 / 100) + 8 * ((3352951 / 10000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13174 166) (d.f1 13174 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13174 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13174 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13174 166) (d.f1 13174 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13174 166) (d.w1 13174 166) (d.w2 13174 166)
  have hwexpr0 : 0 ≤ d.w0 13174 166 + d.w1 13174 166 * √(π / 2) +
      2 * d.w2 13174 166 + energyR16 13174 *
      radiusPolynomialRoot16 (d.w0 13174 166) (d.w1 13174 166) (d.w2 13174 166) := by
    positivity
  constructor
  · change (13174 : ℝ) ^ 8 * (mA 13174 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13174 166) (d.f1 13174 166) d.f2 + locationR16 13174 *
        radiusPolynomialRoot16 (d.f0 13174 166) (d.f1 13174 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13174 : ℝ) ^ 8 * (mA 13174 : ℝ) ^ 8 *
        ((((16334067 / 3906250000000000) : ℝ) ^ 2 + 2 * ((16334067 / 3906250000000000)) * ((55801049 / 40000000000000000)) * (126 / 100) +
          2 * (((55801049 / 40000000000000000)) ^ 2 + 2 * ((16334067 / 3906250000000000)) * ((3352951 / 10000000000000000))) +
          6 * ((55801049 / 40000000000000000)) * ((3352951 / 10000000000000000)) * (126 / 100) + 8 * ((3352951 / 10000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13174) *
          (32 * (((16334067 / 3906250000000000) : ℝ) + (55801049 / 40000000000000000) + (3352951 / 10000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13174 : ℝ) ^ 16 *
      (d.w0 13174 166 + d.w1 13174 166 * √(π / 2) + 2 * d.w2 13174 166 +
        energyR16 13174 * radiusPolynomialRoot16 (d.w0 13174 166) (d.w1 13174 166)
          (d.w2 13174 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13174 : ℝ) ^ 16 *
        (((51323393 / 3125000000000000000) : ℝ) + ((1168499657 / 100000000000000000000)) * (126 / 100) + 2 * ((213469847 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13174) *
          (32 * (((51323393 / 3125000000000000000) : ℝ) + (1168499657 / 100000000000000000000) + (213469847 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13174
