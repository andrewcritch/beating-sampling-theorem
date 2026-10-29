import BstLean.Part266Shard19Step4


/-! A coarse bound on the actual paper statistics constant at dimension 12825. -/
namespace BstLean.Part266.Row12825
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12823 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12823 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12823 128 ≤ (13077 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13077 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12825) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12825 : ℕ))
    (by norm_num : (12825 : ℕ) ≤ 16384)
  have ht : paperTail256 12825 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12825 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12825 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12825 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12825 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12825 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12823 128 * √(2 / (12825 : ℝ)) *
      (√(12825 : ℝ) + paperT0 12825 + paperTail256 12825) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12825 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12825 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12825 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12823 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12823 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12825 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12825

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12825
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12825 (61 / 100) 163 (17 / (100 * 12825)) (26 / (10 * 12825)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12825 (61 / 100) 163 (17 / (100 * 12825)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (92549787 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (721635777 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1182052729 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12825 / 12825 * (61 / 100)) ^ 4 * inverseRadius8 (12825 - 1) /
            envelopeGap 12825 (61 / 100) 163 (17 / (100 * 12825)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12825

namespace BstLean.Part266.Row12825
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12825 163 ≤ (3493629 / 781250000000000)
  f1 : (tableEnvelope C).f1 12825 163 ≤ (59675333 / 40000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (179287371 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12825 163 ≤ (890057361 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12825 163 ≤ (39578677 / 3125000000000000000)
  w2 : (tableEnvelope C).w2 12825 163 ≤ (115688379 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (92549787 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (92549787 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (721635777 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1182052729 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3640791 / 1000000000) : ℝ) ≤ √(17 / (100 * 12825) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12825) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1075580001 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4748801747 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12825) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12825) ≤ (6891879 / 62500000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12825) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12825 * (163 : ℝ) ^ 2 + 26 / (10 * 12825) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12825) : ℝ)) (tA 12825 * 163 ^ 2 + 26 / (10 * 12825)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3640791 / 1000000000))) * ((92549787 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3640791 / 1000000000)) ^ 3) * ((721635777 / 500000000000000000000000))) + ((1182052729 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3640791 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12825) : ℝ)) d.D d.V d.P (√(tA 12825) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3640791 / 1000000000)) ^ 2 * (((1075580001 / 500000000000000)) * ((4748801747 / 125000000000000000)))) + ((1182052729 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12825) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3640791 / 1000000000)) * ((92549787 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12825) : ℝ)) (tA 12825 * 163 ^ 2 + 26 / (10 * 12825)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((92549787 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3640791 / 1000000000)) ^ 2) * ((721635777 / 500000000000000000000000)) + ((1182052729 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12825) : ℝ)) (√(26 / (10 * 12825) : ℝ)) d.D d.V d.P (√(tA 12825) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3640791 / 1000000000)) * (((1075580001 / 500000000000000)) * ((4748801747 / 125000000000000000))) + ((1182052729 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12825) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((92549787 / 20000000000000000000) : ℝ) + ((1182052729 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12825

namespace BstLean.Part266.Row12825
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12825 163 ∧
    0 ≤ (tableEnvelope C).f1 12825 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12825 163 ∧
    0 ≤ (tableEnvelope C).w1 12825 163 ∧ 0 ≤ (tableEnvelope C).w2 12825 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12825 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12825 163 ∧ 0 ≤ d.f1 12825 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12825 163 ∧ 0 ≤ d.w1 12825 163 ∧ 0 ≤ d.w2 12825 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12825 ≤ 2 * (228 / 100 : ℝ) / 12825 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12825 ≤ 2 * (370 / 100 : ℝ) / 12825 := by
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
    (completeRAData (tableEnvelope C) 12825 163).locationBound 12825 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12825 163).energyBound 12825 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12825 163) (d.f1 12825 163) d.f2 ≤
      32 * (((3493629 / 781250000000000) : ℝ) + (59675333 / 40000000000000000) + (179287371 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12825 163) (d.w1 12825 163)
      (d.w2 12825 163) ≤
      32 * (((890057361 / 50000000000000000000) : ℝ) + (39578677 / 3125000000000000000) + (115688379 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12825 163) (d.f1 12825 163) d.f2 ≤
      ((3493629 / 781250000000000) : ℝ) ^ 2 + 2 * ((3493629 / 781250000000000)) * ((59675333 / 40000000000000000)) * (126 / 100) +
      2 * (((59675333 / 40000000000000000)) ^ 2 + 2 * ((3493629 / 781250000000000)) * ((179287371 / 500000000000000000))) +
      6 * ((59675333 / 40000000000000000)) * ((179287371 / 500000000000000000)) * (126 / 100) + 8 * ((179287371 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12825 163) (d.f1 12825 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12825 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12825 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12825 163) (d.f1 12825 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12825 163) (d.w1 12825 163) (d.w2 12825 163)
  have hwexpr0 : 0 ≤ d.w0 12825 163 + d.w1 12825 163 * √(π / 2) +
      2 * d.w2 12825 163 + energyR16 12825 *
      radiusPolynomialRoot16 (d.w0 12825 163) (d.w1 12825 163) (d.w2 12825 163) := by
    positivity
  constructor
  · change (12825 : ℝ) ^ 8 * (mA 12825 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12825 163) (d.f1 12825 163) d.f2 + locationR16 12825 *
        radiusPolynomialRoot16 (d.f0 12825 163) (d.f1 12825 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12825 : ℝ) ^ 8 * (mA 12825 : ℝ) ^ 8 *
        ((((3493629 / 781250000000000) : ℝ) ^ 2 + 2 * ((3493629 / 781250000000000)) * ((59675333 / 40000000000000000)) * (126 / 100) +
          2 * (((59675333 / 40000000000000000)) ^ 2 + 2 * ((3493629 / 781250000000000)) * ((179287371 / 500000000000000000))) +
          6 * ((59675333 / 40000000000000000)) * ((179287371 / 500000000000000000)) * (126 / 100) + 8 * ((179287371 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12825) *
          (32 * (((3493629 / 781250000000000) : ℝ) + (59675333 / 40000000000000000) + (179287371 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12825 : ℝ) ^ 16 *
      (d.w0 12825 163 + d.w1 12825 163 * √(π / 2) + 2 * d.w2 12825 163 +
        energyR16 12825 * radiusPolynomialRoot16 (d.w0 12825 163) (d.w1 12825 163)
          (d.w2 12825 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12825 : ℝ) ^ 16 *
        (((890057361 / 50000000000000000000) : ℝ) + ((39578677 / 3125000000000000000)) * (126 / 100) + 2 * ((115688379 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12825) *
          (32 * (((890057361 / 50000000000000000000) : ℝ) + (39578677 / 3125000000000000000) + (115688379 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12825

/-! A coarse bound on the actual paper statistics constant at dimension 12826. -/
namespace BstLean.Part266.Row12826
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12824 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12824 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12824 128 ≤ (13078 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13078 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12826) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12826 : ℕ))
    (by norm_num : (12826 : ℕ) ≤ 16384)
  have ht : paperTail256 12826 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12826 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12826 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12826 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12826 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12826 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12824 128 * √(2 / (12826 : ℝ)) *
      (√(12826 : ℝ) + paperT0 12826 + paperTail256 12826) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12826 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12826 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12826 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12824 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12824 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12826 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12826

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12826
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12826 (61 / 100) 163 (17 / (100 * 12826)) (26 / (10 * 12826)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12826 (61 / 100) 163 (17 / (100 * 12826)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (462640701 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1442821481 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (590654303 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12826 / 12826 * (61 / 100)) ^ 4 * inverseRadius8 (12826 - 1) /
            envelopeGap 12826 (61 / 100) 163 (17 / (100 * 12826)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12826

namespace BstLean.Part266.Row12826
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12826 163 ≤ (2235486859 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12826 163 ≤ (745796293 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (44813107 / 125000000000000000)
  w0 : (tableEnvelope C).w0 12826 163 ≤ (444924603 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12826 163 ≤ (1266221457 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12826 163 ≤ (462645279 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (462640701 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (462640701 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1442821481 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (590654303 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3640649 / 1000000000) : ℝ) ≤ √(17 / (100 * 12826) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12826) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (4200993 / 1953125000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18992245003 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12826) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12826) ≤ (55130733 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12826) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12826 * (163 : ℝ) ^ 2 + 26 / (10 * 12826) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12826) : ℝ)) (tA 12826 * 163 ^ 2 + 26 / (10 * 12826)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3640649 / 1000000000))) * ((462640701 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3640649 / 1000000000)) ^ 3) * ((1442821481 / 1000000000000000000000000))) + ((590654303 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3640649 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12826) : ℝ)) d.D d.V d.P (√(tA 12826) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3640649 / 1000000000)) ^ 2 * (((4200993 / 1953125000000)) * ((18992245003 / 500000000000000000)))) + ((590654303 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12826) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3640649 / 1000000000)) * ((462640701 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12826) : ℝ)) (tA 12826 * 163 ^ 2 + 26 / (10 * 12826)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((462640701 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3640649 / 1000000000)) ^ 2) * ((1442821481 / 1000000000000000000000000)) + ((590654303 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12826) : ℝ)) (√(26 / (10 * 12826) : ℝ)) d.D d.V d.P (√(tA 12826) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3640649 / 1000000000)) * (((4200993 / 1953125000000)) * ((18992245003 / 500000000000000000))) + ((590654303 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12826) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((462640701 / 100000000000000000000) : ℝ) + ((590654303 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12826

namespace BstLean.Part266.Row12826
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12826 163 ∧
    0 ≤ (tableEnvelope C).f1 12826 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12826 163 ∧
    0 ≤ (tableEnvelope C).w1 12826 163 ∧ 0 ≤ (tableEnvelope C).w2 12826 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12826 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12826 163 ∧ 0 ≤ d.f1 12826 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12826 163 ∧ 0 ≤ d.w1 12826 163 ∧ 0 ≤ d.w2 12826 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12826 ≤ 2 * (228 / 100 : ℝ) / 12826 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12826 ≤ 2 * (370 / 100 : ℝ) / 12826 := by
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
    (completeRAData (tableEnvelope C) 12826 163).locationBound 12826 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12826 163).energyBound 12826 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12826 163) (d.f1 12826 163) d.f2 ≤
      32 * (((2235486859 / 500000000000000000) : ℝ) + (745796293 / 500000000000000000) + (44813107 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12826 163) (d.w1 12826 163)
      (d.w2 12826 163) ≤
      32 * (((444924603 / 25000000000000000000) : ℝ) + (1266221457 / 100000000000000000000) + (462645279 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12826 163) (d.f1 12826 163) d.f2 ≤
      ((2235486859 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2235486859 / 500000000000000000)) * ((745796293 / 500000000000000000)) * (126 / 100) +
      2 * (((745796293 / 500000000000000000)) ^ 2 + 2 * ((2235486859 / 500000000000000000)) * ((44813107 / 125000000000000000))) +
      6 * ((745796293 / 500000000000000000)) * ((44813107 / 125000000000000000)) * (126 / 100) + 8 * ((44813107 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12826 163) (d.f1 12826 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12826 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12826 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12826 163) (d.f1 12826 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12826 163) (d.w1 12826 163) (d.w2 12826 163)
  have hwexpr0 : 0 ≤ d.w0 12826 163 + d.w1 12826 163 * √(π / 2) +
      2 * d.w2 12826 163 + energyR16 12826 *
      radiusPolynomialRoot16 (d.w0 12826 163) (d.w1 12826 163) (d.w2 12826 163) := by
    positivity
  constructor
  · change (12826 : ℝ) ^ 8 * (mA 12826 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12826 163) (d.f1 12826 163) d.f2 + locationR16 12826 *
        radiusPolynomialRoot16 (d.f0 12826 163) (d.f1 12826 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12826 : ℝ) ^ 8 * (mA 12826 : ℝ) ^ 8 *
        ((((2235486859 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2235486859 / 500000000000000000)) * ((745796293 / 500000000000000000)) * (126 / 100) +
          2 * (((745796293 / 500000000000000000)) ^ 2 + 2 * ((2235486859 / 500000000000000000)) * ((44813107 / 125000000000000000))) +
          6 * ((745796293 / 500000000000000000)) * ((44813107 / 125000000000000000)) * (126 / 100) + 8 * ((44813107 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12826) *
          (32 * (((2235486859 / 500000000000000000) : ℝ) + (745796293 / 500000000000000000) + (44813107 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12826 : ℝ) ^ 16 *
      (d.w0 12826 163 + d.w1 12826 163 * √(π / 2) + 2 * d.w2 12826 163 +
        energyR16 12826 * radiusPolynomialRoot16 (d.w0 12826 163) (d.w1 12826 163)
          (d.w2 12826 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12826 : ℝ) ^ 16 *
        (((444924603 / 25000000000000000000) : ℝ) + ((1266221457 / 100000000000000000000)) * (126 / 100) + 2 * ((462645279 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12826) *
          (32 * (((444924603 / 25000000000000000000) : ℝ) + (1266221457 / 100000000000000000000) + (462645279 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12826

/-! A coarse bound on the actual paper statistics constant at dimension 12827. -/
namespace BstLean.Part266.Row12827
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12825 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12825 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12825 128 ≤ (13079 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13079 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12827) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12827 : ℕ))
    (by norm_num : (12827 : ℕ) ≤ 16384)
  have ht : paperTail256 12827 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12827 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12827 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12827 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12827 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12827 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12825 128 * √(2 / (12827 : ℝ)) *
      (√(12827 : ℝ) + paperT0 12827 + paperTail256 12827) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12827 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12827 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12827 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12825 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12825 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12827 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12827

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12827
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12827 (61 / 100) 163 (17 / (100 * 12827)) (26 / (10 * 12827)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12827 (61 / 100) 163 (17 / (100 * 12827)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (462532501 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1442371583 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2361130021 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12827 / 12827 * (61 / 100)) ^ 4 * inverseRadius8 (12827 - 1) /
            envelopeGap 12827 (61 / 100) 163 (17 / (100 * 12827)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12827

namespace BstLean.Part266.Row12827
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12827 163 ≤ (4470102611 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12827 163 ≤ (1491301939 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (22402187 / 62500000000000000)
  w0 : (tableEnvelope C).w0 12827 163 ≤ (444820561 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12827 163 ≤ (1265925347 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12827 163 ≤ (115634269 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (462532501 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (462532501 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1442371583 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2361130021 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3640507 / 1000000000) : ℝ) ≤ √(17 / (100 * 12827) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12827) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2150656879 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37978567417 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12827) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12827) ≤ (11025287 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12827) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12827 * (163 : ℝ) ^ 2 + 26 / (10 * 12827) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12827) : ℝ)) (tA 12827 * 163 ^ 2 + 26 / (10 * 12827)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3640507 / 1000000000))) * ((462532501 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3640507 / 1000000000)) ^ 3) * ((1442371583 / 1000000000000000000000000))) + ((2361130021 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3640507 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12827) : ℝ)) d.D d.V d.P (√(tA 12827) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3640507 / 1000000000)) ^ 2 * (((2150656879 / 1000000000000000)) * ((37978567417 / 1000000000000000000)))) + ((2361130021 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12827) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3640507 / 1000000000)) * ((462532501 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12827) : ℝ)) (tA 12827 * 163 ^ 2 + 26 / (10 * 12827)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((462532501 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3640507 / 1000000000)) ^ 2) * ((1442371583 / 1000000000000000000000000)) + ((2361130021 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12827) : ℝ)) (√(26 / (10 * 12827) : ℝ)) d.D d.V d.P (√(tA 12827) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3640507 / 1000000000)) * (((2150656879 / 1000000000000000)) * ((37978567417 / 1000000000000000000))) + ((2361130021 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12827) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((462532501 / 100000000000000000000) : ℝ) + ((2361130021 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12827

namespace BstLean.Part266.Row12827
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12827 163 ∧
    0 ≤ (tableEnvelope C).f1 12827 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12827 163 ∧
    0 ≤ (tableEnvelope C).w1 12827 163 ∧ 0 ≤ (tableEnvelope C).w2 12827 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12827 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12827 163 ∧ 0 ≤ d.f1 12827 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12827 163 ∧ 0 ≤ d.w1 12827 163 ∧ 0 ≤ d.w2 12827 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12827 ≤ 2 * (228 / 100 : ℝ) / 12827 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12827 ≤ 2 * (370 / 100 : ℝ) / 12827 := by
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
    (completeRAData (tableEnvelope C) 12827 163).locationBound 12827 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12827 163).energyBound 12827 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12827 163) (d.f1 12827 163) d.f2 ≤
      32 * (((4470102611 / 1000000000000000000) : ℝ) + (1491301939 / 1000000000000000000) + (22402187 / 62500000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12827 163) (d.w1 12827 163)
      (d.w2 12827 163) ≤
      32 * (((444820561 / 25000000000000000000) : ℝ) + (1265925347 / 100000000000000000000) + (115634269 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12827 163) (d.f1 12827 163) d.f2 ≤
      ((4470102611 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4470102611 / 1000000000000000000)) * ((1491301939 / 1000000000000000000)) * (126 / 100) +
      2 * (((1491301939 / 1000000000000000000)) ^ 2 + 2 * ((4470102611 / 1000000000000000000)) * ((22402187 / 62500000000000000))) +
      6 * ((1491301939 / 1000000000000000000)) * ((22402187 / 62500000000000000)) * (126 / 100) + 8 * ((22402187 / 62500000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12827 163) (d.f1 12827 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12827 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12827 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12827 163) (d.f1 12827 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12827 163) (d.w1 12827 163) (d.w2 12827 163)
  have hwexpr0 : 0 ≤ d.w0 12827 163 + d.w1 12827 163 * √(π / 2) +
      2 * d.w2 12827 163 + energyR16 12827 *
      radiusPolynomialRoot16 (d.w0 12827 163) (d.w1 12827 163) (d.w2 12827 163) := by
    positivity
  constructor
  · change (12827 : ℝ) ^ 8 * (mA 12827 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12827 163) (d.f1 12827 163) d.f2 + locationR16 12827 *
        radiusPolynomialRoot16 (d.f0 12827 163) (d.f1 12827 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12827 : ℝ) ^ 8 * (mA 12827 : ℝ) ^ 8 *
        ((((4470102611 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4470102611 / 1000000000000000000)) * ((1491301939 / 1000000000000000000)) * (126 / 100) +
          2 * (((1491301939 / 1000000000000000000)) ^ 2 + 2 * ((4470102611 / 1000000000000000000)) * ((22402187 / 62500000000000000))) +
          6 * ((1491301939 / 1000000000000000000)) * ((22402187 / 62500000000000000)) * (126 / 100) + 8 * ((22402187 / 62500000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12827) *
          (32 * (((4470102611 / 1000000000000000000) : ℝ) + (1491301939 / 1000000000000000000) + (22402187 / 62500000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12827 : ℝ) ^ 16 *
      (d.w0 12827 163 + d.w1 12827 163 * √(π / 2) + 2 * d.w2 12827 163 +
        energyR16 12827 * radiusPolynomialRoot16 (d.w0 12827 163) (d.w1 12827 163)
          (d.w2 12827 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12827 : ℝ) ^ 16 *
        (((444820561 / 25000000000000000000) : ℝ) + ((1265925347 / 100000000000000000000)) * (126 / 100) + 2 * ((115634269 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12827) *
          (32 * (((444820561 / 25000000000000000000) : ℝ) + (1265925347 / 100000000000000000000) + (115634269 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12827

/-! A coarse bound on the actual paper statistics constant at dimension 12828. -/
namespace BstLean.Part266.Row12828
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12826 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12826 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12826 128 ≤ (13080 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13080 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12828) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12828 : ℕ))
    (by norm_num : (12828 : ℕ) ≤ 16384)
  have ht : paperTail256 12828 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12828 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12828 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12828 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12828 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12828 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12826 128 * √(2 / (12828 : ℝ)) *
      (√(12828 : ℝ) + paperT0 12828 + paperTail256 12828) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12828 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12828 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12828 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12826 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12826 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12828 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12828

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12828
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12828 (61 / 100) 164 (17 / (100 * 12828)) (26 / (10 * 12828)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12828 (61 / 100) 164 (17 / (100 * 12828)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (231212167 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1441921861 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (295090769 / 62500000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12828 / 12828 * (61 / 100)) ^ 4 * inverseRadius8 (12828 - 1) /
            envelopeGap 12828 (61 / 100) 164 (17 / (100 * 12828)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12828

namespace BstLean.Part266.Row12828
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12828 164 ≤ (2234615901 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12828 164 ≤ (745505693 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (358365147 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12828 164 ≤ (1778866219 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12828 164 ≤ (158203667 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 12828 164 ≤ (115607227 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (231212167 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (231212167 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1441921861 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (295090769 / 62500000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((728073 / 200000000) : ℝ) ≤ √(17 / (100 * 12828) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12828) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (215040539 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37972646221 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12828) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12828) ≤ (27561069 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12828) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12828 * (164 : ℝ) ^ 2 + 26 / (10 * 12828) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12828) : ℝ)) (tA 12828 * 164 ^ 2 + 26 / (10 * 12828)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((728073 / 200000000))) * ((231212167 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((728073 / 200000000)) ^ 3) * ((1441921861 / 1000000000000000000000000))) + ((295090769 / 62500000000000000000000)) * (3 / 2 * (39895 / 100000) / ((728073 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12828) : ℝ)) d.D d.V d.P (√(tA 12828) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((728073 / 200000000)) ^ 2 * (((215040539 / 100000000000000)) * ((37972646221 / 1000000000000000000)))) + ((295090769 / 62500000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12828) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((728073 / 200000000)) * ((231212167 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12828) : ℝ)) (tA 12828 * 164 ^ 2 + 26 / (10 * 12828)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((231212167 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((728073 / 200000000)) ^ 2) * ((1441921861 / 1000000000000000000000000)) + ((295090769 / 62500000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12828) : ℝ)) (√(26 / (10 * 12828) : ℝ)) d.D d.V d.P (√(tA 12828) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((728073 / 200000000)) * (((215040539 / 100000000000000)) * ((37972646221 / 1000000000000000000))) + ((295090769 / 62500000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12828) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((231212167 / 50000000000000000000) : ℝ) + ((295090769 / 62500000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12828

namespace BstLean.Part266.Row12828
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12828 164 ∧
    0 ≤ (tableEnvelope C).f1 12828 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12828 164 ∧
    0 ≤ (tableEnvelope C).w1 12828 164 ∧ 0 ≤ (tableEnvelope C).w2 12828 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12828 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12828 164 ∧ 0 ≤ d.f1 12828 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12828 164 ∧ 0 ≤ d.w1 12828 164 ∧ 0 ≤ d.w2 12828 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12828 ≤ 2 * (228 / 100 : ℝ) / 12828 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12828 ≤ 2 * (370 / 100 : ℝ) / 12828 := by
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
    (completeRAData (tableEnvelope C) 12828 164).locationBound 12828 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12828 164).energyBound 12828 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12828 164) (d.f1 12828 164) d.f2 ≤
      32 * (((2234615901 / 500000000000000000) : ℝ) + (745505693 / 500000000000000000) + (358365147 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12828 164) (d.w1 12828 164)
      (d.w2 12828 164) ≤
      32 * (((1778866219 / 100000000000000000000) : ℝ) + (158203667 / 12500000000000000000) + (115607227 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12828 164) (d.f1 12828 164) d.f2 ≤
      ((2234615901 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2234615901 / 500000000000000000)) * ((745505693 / 500000000000000000)) * (126 / 100) +
      2 * (((745505693 / 500000000000000000)) ^ 2 + 2 * ((2234615901 / 500000000000000000)) * ((358365147 / 1000000000000000000))) +
      6 * ((745505693 / 500000000000000000)) * ((358365147 / 1000000000000000000)) * (126 / 100) + 8 * ((358365147 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12828 164) (d.f1 12828 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12828 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12828 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12828 164) (d.f1 12828 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12828 164) (d.w1 12828 164) (d.w2 12828 164)
  have hwexpr0 : 0 ≤ d.w0 12828 164 + d.w1 12828 164 * √(π / 2) +
      2 * d.w2 12828 164 + energyR16 12828 *
      radiusPolynomialRoot16 (d.w0 12828 164) (d.w1 12828 164) (d.w2 12828 164) := by
    positivity
  constructor
  · change (12828 : ℝ) ^ 8 * (mA 12828 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12828 164) (d.f1 12828 164) d.f2 + locationR16 12828 *
        radiusPolynomialRoot16 (d.f0 12828 164) (d.f1 12828 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12828 : ℝ) ^ 8 * (mA 12828 : ℝ) ^ 8 *
        ((((2234615901 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2234615901 / 500000000000000000)) * ((745505693 / 500000000000000000)) * (126 / 100) +
          2 * (((745505693 / 500000000000000000)) ^ 2 + 2 * ((2234615901 / 500000000000000000)) * ((358365147 / 1000000000000000000))) +
          6 * ((745505693 / 500000000000000000)) * ((358365147 / 1000000000000000000)) * (126 / 100) + 8 * ((358365147 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12828) *
          (32 * (((2234615901 / 500000000000000000) : ℝ) + (745505693 / 500000000000000000) + (358365147 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12828 : ℝ) ^ 16 *
      (d.w0 12828 164 + d.w1 12828 164 * √(π / 2) + 2 * d.w2 12828 164 +
        energyR16 12828 * radiusPolynomialRoot16 (d.w0 12828 164) (d.w1 12828 164)
          (d.w2 12828 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12828 : ℝ) ^ 16 *
        (((1778866219 / 100000000000000000000) : ℝ) + ((158203667 / 12500000000000000000)) * (126 / 100) + 2 * ((115607227 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12828) *
          (32 * (((1778866219 / 100000000000000000000) : ℝ) + (158203667 / 12500000000000000000) + (115607227 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12828

/-! A coarse bound on the actual paper statistics constant at dimension 12829. -/
namespace BstLean.Part266.Row12829
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12827 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12827 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12827 128 ≤ (13081 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13081 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12829) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12829 : ℕ))
    (by norm_num : (12829 : ℕ) ≤ 16384)
  have ht : paperTail256 12829 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12829 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12829 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12829 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12829 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12829 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12827 128 * √(2 / (12829 : ℝ)) *
      (√(12829 : ℝ) + paperT0 12829 + paperTail256 12829) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12829 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12829 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12829 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12827 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12827 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12829 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12829

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12829
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12829 (61 / 100) 164 (17 / (100 * 12829)) (26 / (10 * 12829)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12829 (61 / 100) 164 (17 / (100 * 12829)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (462316201 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (720736157 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1179620109 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12829 / 12829 * (61 / 100)) ^ 4 * inverseRadius8 (12829 - 1) /
            envelopeGap 12829 (61 / 100) 164 (17 / (100 * 12829)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12829

namespace BstLean.Part266.Row12829
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12829 164 ≤ (4468361289 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12829 164 ≤ (59628837 / 40000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (358295323 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12829 164 ≤ (889225167 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12829 164 ≤ (1265333423 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12829 164 ≤ (115580193 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (462316201 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (462316201 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (720736157 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1179620109 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3640223 / 1000000000) : ℝ) ≤ √(17 / (100 * 12829) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12829) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2150153951 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37966726407 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12829) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12829) ≤ (55117841 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12829) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12829 * (164 : ℝ) ^ 2 + 26 / (10 * 12829) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12829) : ℝ)) (tA 12829 * 164 ^ 2 + 26 / (10 * 12829)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3640223 / 1000000000))) * ((462316201 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3640223 / 1000000000)) ^ 3) * ((720736157 / 500000000000000000000000))) + ((1179620109 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3640223 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12829) : ℝ)) d.D d.V d.P (√(tA 12829) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3640223 / 1000000000)) ^ 2 * (((2150153951 / 1000000000000000)) * ((37966726407 / 1000000000000000000)))) + ((1179620109 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12829) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3640223 / 1000000000)) * ((462316201 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12829) : ℝ)) (tA 12829 * 164 ^ 2 + 26 / (10 * 12829)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((462316201 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3640223 / 1000000000)) ^ 2) * ((720736157 / 500000000000000000000000)) + ((1179620109 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12829) : ℝ)) (√(26 / (10 * 12829) : ℝ)) d.D d.V d.P (√(tA 12829) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3640223 / 1000000000)) * (((2150153951 / 1000000000000000)) * ((37966726407 / 1000000000000000000))) + ((1179620109 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12829) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((462316201 / 100000000000000000000) : ℝ) + ((1179620109 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12829

namespace BstLean.Part266.Row12829
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12829 164 ∧
    0 ≤ (tableEnvelope C).f1 12829 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12829 164 ∧
    0 ≤ (tableEnvelope C).w1 12829 164 ∧ 0 ≤ (tableEnvelope C).w2 12829 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12829 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12829 164 ∧ 0 ≤ d.f1 12829 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12829 164 ∧ 0 ≤ d.w1 12829 164 ∧ 0 ≤ d.w2 12829 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12829 ≤ 2 * (228 / 100 : ℝ) / 12829 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12829 ≤ 2 * (370 / 100 : ℝ) / 12829 := by
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
    (completeRAData (tableEnvelope C) 12829 164).locationBound 12829 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12829 164).energyBound 12829 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12829 164) (d.f1 12829 164) d.f2 ≤
      32 * (((4468361289 / 1000000000000000000) : ℝ) + (59628837 / 40000000000000000) + (358295323 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12829 164) (d.w1 12829 164)
      (d.w2 12829 164) ≤
      32 * (((889225167 / 50000000000000000000) : ℝ) + (1265333423 / 100000000000000000000) + (115580193 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12829 164) (d.f1 12829 164) d.f2 ≤
      ((4468361289 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4468361289 / 1000000000000000000)) * ((59628837 / 40000000000000000)) * (126 / 100) +
      2 * (((59628837 / 40000000000000000)) ^ 2 + 2 * ((4468361289 / 1000000000000000000)) * ((358295323 / 1000000000000000000))) +
      6 * ((59628837 / 40000000000000000)) * ((358295323 / 1000000000000000000)) * (126 / 100) + 8 * ((358295323 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12829 164) (d.f1 12829 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12829 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12829 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12829 164) (d.f1 12829 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12829 164) (d.w1 12829 164) (d.w2 12829 164)
  have hwexpr0 : 0 ≤ d.w0 12829 164 + d.w1 12829 164 * √(π / 2) +
      2 * d.w2 12829 164 + energyR16 12829 *
      radiusPolynomialRoot16 (d.w0 12829 164) (d.w1 12829 164) (d.w2 12829 164) := by
    positivity
  constructor
  · change (12829 : ℝ) ^ 8 * (mA 12829 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12829 164) (d.f1 12829 164) d.f2 + locationR16 12829 *
        radiusPolynomialRoot16 (d.f0 12829 164) (d.f1 12829 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12829 : ℝ) ^ 8 * (mA 12829 : ℝ) ^ 8 *
        ((((4468361289 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4468361289 / 1000000000000000000)) * ((59628837 / 40000000000000000)) * (126 / 100) +
          2 * (((59628837 / 40000000000000000)) ^ 2 + 2 * ((4468361289 / 1000000000000000000)) * ((358295323 / 1000000000000000000))) +
          6 * ((59628837 / 40000000000000000)) * ((358295323 / 1000000000000000000)) * (126 / 100) + 8 * ((358295323 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12829) *
          (32 * (((4468361289 / 1000000000000000000) : ℝ) + (59628837 / 40000000000000000) + (358295323 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12829 : ℝ) ^ 16 *
      (d.w0 12829 164 + d.w1 12829 164 * √(π / 2) + 2 * d.w2 12829 164 +
        energyR16 12829 * radiusPolynomialRoot16 (d.w0 12829 164) (d.w1 12829 164)
          (d.w2 12829 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12829 : ℝ) ^ 16 *
        (((889225167 / 50000000000000000000) : ℝ) + ((1265333423 / 100000000000000000000)) * (126 / 100) + 2 * ((115580193 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12829) *
          (32 * (((889225167 / 50000000000000000000) : ℝ) + (1265333423 / 100000000000000000000) + (115580193 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12829

/-! A coarse bound on the actual paper statistics constant at dimension 12830. -/
namespace BstLean.Part266.Row12830
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12828 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12828 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12828 128 ≤ (13082 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13082 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12830) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12830 : ℕ))
    (by norm_num : (12830 : ℕ) ≤ 16384)
  have ht : paperTail256 12830 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12830 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12830 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12830 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12830 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12830 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12828 128 * √(2 / (12830 : ℝ)) *
      (√(12830 : ℝ) + paperT0 12830 + paperTail256 12830) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12830 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12830 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12830 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12828 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12828 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12830 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12830

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12830
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12830 (61 / 100) 164 (17 / (100 * 12830)) (26 / (10 * 12830)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12830 (61 / 100) 164 (17 / (100 * 12830)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (231104051 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (720511471 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2357755337 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12830 / 12830 * (61 / 100)) ^ 4 * inverseRadius8 (12830 - 1) /
            envelopeGap 12830 (61 / 100) 164 (17 / (100 * 12830)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12830

namespace BstLean.Part266.Row12830
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12830 164 ≤ (17451137 / 3906250000000000)
  f1 : (tableEnvelope C).f1 12830 164 ≤ (745215279 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (4477819 / 12500000000000000)
  w0 : (tableEnvelope C).w0 12830 164 ≤ (1778034591 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12830 164 ≤ (1265037607 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12830 164 ≤ (46221267 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (231104051 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (231104051 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (720511471 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2357755337 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3640081 / 1000000000) : ℝ) ≤ √(17 / (100 * 12830) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12830) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2149902561 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18980403987 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12830) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12830) ≤ (11022709 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12830) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12830 * (164 : ℝ) ^ 2 + 26 / (10 * 12830) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12830) : ℝ)) (tA 12830 * 164 ^ 2 + 26 / (10 * 12830)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3640081 / 1000000000))) * ((231104051 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3640081 / 1000000000)) ^ 3) * ((720511471 / 500000000000000000000000))) + ((2357755337 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3640081 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12830) : ℝ)) d.D d.V d.P (√(tA 12830) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3640081 / 1000000000)) ^ 2 * (((2149902561 / 1000000000000000)) * ((18980403987 / 500000000000000000)))) + ((2357755337 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12830) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3640081 / 1000000000)) * ((231104051 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12830) : ℝ)) (tA 12830 * 164 ^ 2 + 26 / (10 * 12830)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((231104051 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3640081 / 1000000000)) ^ 2) * ((720511471 / 500000000000000000000000)) + ((2357755337 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12830) : ℝ)) (√(26 / (10 * 12830) : ℝ)) d.D d.V d.P (√(tA 12830) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3640081 / 1000000000)) * (((2149902561 / 1000000000000000)) * ((18980403987 / 500000000000000000))) + ((2357755337 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12830) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((231104051 / 50000000000000000000) : ℝ) + ((2357755337 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12830

namespace BstLean.Part266.Row12830
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12830 164 ∧
    0 ≤ (tableEnvelope C).f1 12830 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12830 164 ∧
    0 ≤ (tableEnvelope C).w1 12830 164 ∧ 0 ≤ (tableEnvelope C).w2 12830 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12830 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12830 164 ∧ 0 ≤ d.f1 12830 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12830 164 ∧ 0 ≤ d.w1 12830 164 ∧ 0 ≤ d.w2 12830 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12830 ≤ 2 * (228 / 100 : ℝ) / 12830 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12830 ≤ 2 * (370 / 100 : ℝ) / 12830 := by
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
    (completeRAData (tableEnvelope C) 12830 164).locationBound 12830 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12830 164).energyBound 12830 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12830 164) (d.f1 12830 164) d.f2 ≤
      32 * (((17451137 / 3906250000000000) : ℝ) + (745215279 / 500000000000000000) + (4477819 / 12500000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12830 164) (d.w1 12830 164)
      (d.w2 12830 164) ≤
      32 * (((1778034591 / 100000000000000000000) : ℝ) + (1265037607 / 100000000000000000000) + (46221267 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12830 164) (d.f1 12830 164) d.f2 ≤
      ((17451137 / 3906250000000000) : ℝ) ^ 2 + 2 * ((17451137 / 3906250000000000)) * ((745215279 / 500000000000000000)) * (126 / 100) +
      2 * (((745215279 / 500000000000000000)) ^ 2 + 2 * ((17451137 / 3906250000000000)) * ((4477819 / 12500000000000000))) +
      6 * ((745215279 / 500000000000000000)) * ((4477819 / 12500000000000000)) * (126 / 100) + 8 * ((4477819 / 12500000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12830 164) (d.f1 12830 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12830 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12830 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12830 164) (d.f1 12830 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12830 164) (d.w1 12830 164) (d.w2 12830 164)
  have hwexpr0 : 0 ≤ d.w0 12830 164 + d.w1 12830 164 * √(π / 2) +
      2 * d.w2 12830 164 + energyR16 12830 *
      radiusPolynomialRoot16 (d.w0 12830 164) (d.w1 12830 164) (d.w2 12830 164) := by
    positivity
  constructor
  · change (12830 : ℝ) ^ 8 * (mA 12830 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12830 164) (d.f1 12830 164) d.f2 + locationR16 12830 *
        radiusPolynomialRoot16 (d.f0 12830 164) (d.f1 12830 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12830 : ℝ) ^ 8 * (mA 12830 : ℝ) ^ 8 *
        ((((17451137 / 3906250000000000) : ℝ) ^ 2 + 2 * ((17451137 / 3906250000000000)) * ((745215279 / 500000000000000000)) * (126 / 100) +
          2 * (((745215279 / 500000000000000000)) ^ 2 + 2 * ((17451137 / 3906250000000000)) * ((4477819 / 12500000000000000))) +
          6 * ((745215279 / 500000000000000000)) * ((4477819 / 12500000000000000)) * (126 / 100) + 8 * ((4477819 / 12500000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12830) *
          (32 * (((17451137 / 3906250000000000) : ℝ) + (745215279 / 500000000000000000) + (4477819 / 12500000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12830 : ℝ) ^ 16 *
      (d.w0 12830 164 + d.w1 12830 164 * √(π / 2) + 2 * d.w2 12830 164 +
        energyR16 12830 * radiusPolynomialRoot16 (d.w0 12830 164) (d.w1 12830 164)
          (d.w2 12830 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12830 : ℝ) ^ 16 *
        (((1778034591 / 100000000000000000000) : ℝ) + ((1265037607 / 100000000000000000000)) * (126 / 100) + 2 * ((46221267 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12830) *
          (32 * (((1778034591 / 100000000000000000000) : ℝ) + (1265037607 / 100000000000000000000) + (46221267 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12830

/-! A coarse bound on the actual paper statistics constant at dimension 12831. -/
namespace BstLean.Part266.Row12831
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12829 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12829 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12829 128 ≤ (13083 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13083 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12831) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12831 : ℕ))
    (by norm_num : (12831 : ℕ) ≤ 16384)
  have ht : paperTail256 12831 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12831 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12831 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12831 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12831 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12831 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12829 128 * √(2 / (12831 : ℝ)) *
      (√(12831 : ℝ) + paperT0 12831 + paperTail256 12831) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12831 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12831 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12831 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12829 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12829 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12831 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12831

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12831
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12831 (61 / 100) 164 (17 / (100 * 12831)) (26 / (10 * 12831)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12831 (61 / 100) 164 (17 / (100 * 12831)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (462100037 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (720286873 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (589067877 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12831 / 12831 * (61 / 100)) ^ 4 * inverseRadius8 (12831 - 1) /
            envelopeGap 12831 (61 / 100) 164 (17 / (100 * 12831)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12831

namespace BstLean.Part266.Row12831
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12831 164 ≤ (4466621153 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12831 164 ≤ (372535071 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (179077869 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12831 164 ≤ (1777618991 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12831 164 ≤ (1264741891 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12831 164 ≤ (231052301 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (462100037 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (462100037 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (720286873 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (589067877 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3639939 / 1000000000) : ℝ) ≤ √(17 / (100 * 12831) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12831) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2149651221 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37954890937 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12831) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12831) ≤ (220437 / 2000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12831) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12831 * (164 : ℝ) ^ 2 + 26 / (10 * 12831) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12831) : ℝ)) (tA 12831 * 164 ^ 2 + 26 / (10 * 12831)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3639939 / 1000000000))) * ((462100037 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3639939 / 1000000000)) ^ 3) * ((720286873 / 500000000000000000000000))) + ((589067877 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3639939 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12831) : ℝ)) d.D d.V d.P (√(tA 12831) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3639939 / 1000000000)) ^ 2 * (((2149651221 / 1000000000000000)) * ((37954890937 / 1000000000000000000)))) + ((589067877 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12831) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3639939 / 1000000000)) * ((462100037 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12831) : ℝ)) (tA 12831 * 164 ^ 2 + 26 / (10 * 12831)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((462100037 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3639939 / 1000000000)) ^ 2) * ((720286873 / 500000000000000000000000)) + ((589067877 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12831) : ℝ)) (√(26 / (10 * 12831) : ℝ)) d.D d.V d.P (√(tA 12831) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3639939 / 1000000000)) * (((2149651221 / 1000000000000000)) * ((37954890937 / 1000000000000000000))) + ((589067877 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12831) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((462100037 / 100000000000000000000) : ℝ) + ((589067877 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12831

namespace BstLean.Part266.Row12831
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12831 164 ∧
    0 ≤ (tableEnvelope C).f1 12831 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12831 164 ∧
    0 ≤ (tableEnvelope C).w1 12831 164 ∧ 0 ≤ (tableEnvelope C).w2 12831 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12831 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12831 164 ∧ 0 ≤ d.f1 12831 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12831 164 ∧ 0 ≤ d.w1 12831 164 ∧ 0 ≤ d.w2 12831 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12831 ≤ 2 * (228 / 100 : ℝ) / 12831 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12831 ≤ 2 * (370 / 100 : ℝ) / 12831 := by
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
    (completeRAData (tableEnvelope C) 12831 164).locationBound 12831 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12831 164).energyBound 12831 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12831 164) (d.f1 12831 164) d.f2 ≤
      32 * (((4466621153 / 1000000000000000000) : ℝ) + (372535071 / 250000000000000000) + (179077869 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12831 164) (d.w1 12831 164)
      (d.w2 12831 164) ≤
      32 * (((1777618991 / 100000000000000000000) : ℝ) + (1264741891 / 100000000000000000000) + (231052301 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12831 164) (d.f1 12831 164) d.f2 ≤
      ((4466621153 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4466621153 / 1000000000000000000)) * ((372535071 / 250000000000000000)) * (126 / 100) +
      2 * (((372535071 / 250000000000000000)) ^ 2 + 2 * ((4466621153 / 1000000000000000000)) * ((179077869 / 500000000000000000))) +
      6 * ((372535071 / 250000000000000000)) * ((179077869 / 500000000000000000)) * (126 / 100) + 8 * ((179077869 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12831 164) (d.f1 12831 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12831 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12831 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12831 164) (d.f1 12831 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12831 164) (d.w1 12831 164) (d.w2 12831 164)
  have hwexpr0 : 0 ≤ d.w0 12831 164 + d.w1 12831 164 * √(π / 2) +
      2 * d.w2 12831 164 + energyR16 12831 *
      radiusPolynomialRoot16 (d.w0 12831 164) (d.w1 12831 164) (d.w2 12831 164) := by
    positivity
  constructor
  · change (12831 : ℝ) ^ 8 * (mA 12831 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12831 164) (d.f1 12831 164) d.f2 + locationR16 12831 *
        radiusPolynomialRoot16 (d.f0 12831 164) (d.f1 12831 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12831 : ℝ) ^ 8 * (mA 12831 : ℝ) ^ 8 *
        ((((4466621153 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4466621153 / 1000000000000000000)) * ((372535071 / 250000000000000000)) * (126 / 100) +
          2 * (((372535071 / 250000000000000000)) ^ 2 + 2 * ((4466621153 / 1000000000000000000)) * ((179077869 / 500000000000000000))) +
          6 * ((372535071 / 250000000000000000)) * ((179077869 / 500000000000000000)) * (126 / 100) + 8 * ((179077869 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12831) *
          (32 * (((4466621153 / 1000000000000000000) : ℝ) + (372535071 / 250000000000000000) + (179077869 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12831 : ℝ) ^ 16 *
      (d.w0 12831 164 + d.w1 12831 164 * √(π / 2) + 2 * d.w2 12831 164 +
        energyR16 12831 * radiusPolynomialRoot16 (d.w0 12831 164) (d.w1 12831 164)
          (d.w2 12831 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12831 : ℝ) ^ 16 *
        (((1777618991 / 100000000000000000000) : ℝ) + ((1264741891 / 100000000000000000000)) * (126 / 100) + 2 * ((231052301 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12831) *
          (32 * (((1777618991 / 100000000000000000000) : ℝ) + (1264741891 / 100000000000000000000) + (231052301 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12831

/-! A coarse bound on the actual paper statistics constant at dimension 12832. -/
namespace BstLean.Part266.Row12832
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12830 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12830 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12830 128 ≤ (13084 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13084 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12832) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12832 : ℕ))
    (by norm_num : (12832 : ℕ) ≤ 16384)
  have ht : paperTail256 12832 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12832 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12832 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12832 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12832 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12832 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12830 128 * √(2 / (12832 : ℝ)) *
      (√(12832 : ℝ) + paperT0 12832 + paperTail256 12832) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12832 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12832 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12832 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12830 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12830 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12832 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12832

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12832
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12832 (61 / 100) 164 (17 / (100 * 12832)) (26 / (10 * 12832)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12832 (61 / 100) 164 (17 / (100 * 12832)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (92398401 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (360031181 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2354788731 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12832 / 12832 * (61 / 100)) ^ 4 * inverseRadius8 (12832 - 1) /
            envelopeGap 12832 (61 / 100) 164 (17 / (100 * 12832)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12832

namespace BstLean.Part266.Row12832
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12832 164 ≤ (2232873993 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12832 164 ≤ (1489849283 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (179042939 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12832 164 ≤ (222150351 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 12832 164 ≤ (316111481 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12832 164 ≤ (57749571 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (92398401 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (92398401 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (360031181 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2354788731 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1819899 / 500000000) : ℝ) ≤ √(17 / (100 * 12832) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12832) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (268674991 / 125000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3794897527 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12832) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12832) ≤ (11020991 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12832) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12832 * (164 : ℝ) ^ 2 + 26 / (10 * 12832) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12832) : ℝ)) (tA 12832 * 164 ^ 2 + 26 / (10 * 12832)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1819899 / 500000000))) * ((92398401 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1819899 / 500000000)) ^ 3) * ((360031181 / 250000000000000000000000))) + ((2354788731 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1819899 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12832) : ℝ)) d.D d.V d.P (√(tA 12832) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1819899 / 500000000)) ^ 2 * (((268674991 / 125000000000000)) * ((3794897527 / 100000000000000000)))) + ((2354788731 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12832) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1819899 / 500000000)) * ((92398401 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12832) : ℝ)) (tA 12832 * 164 ^ 2 + 26 / (10 * 12832)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((92398401 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1819899 / 500000000)) ^ 2) * ((360031181 / 250000000000000000000000)) + ((2354788731 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12832) : ℝ)) (√(26 / (10 * 12832) : ℝ)) d.D d.V d.P (√(tA 12832) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1819899 / 500000000)) * (((268674991 / 125000000000000)) * ((3794897527 / 100000000000000000))) + ((2354788731 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12832) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((92398401 / 20000000000000000000) : ℝ) + ((2354788731 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12832

namespace BstLean.Part266.Row12832
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12832 164 ∧
    0 ≤ (tableEnvelope C).f1 12832 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12832 164 ∧
    0 ≤ (tableEnvelope C).w1 12832 164 ∧ 0 ≤ (tableEnvelope C).w2 12832 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12832 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12832 164 ∧ 0 ≤ d.f1 12832 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12832 164 ∧ 0 ≤ d.w1 12832 164 ∧ 0 ≤ d.w2 12832 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12832 ≤ 2 * (228 / 100 : ℝ) / 12832 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12832 ≤ 2 * (370 / 100 : ℝ) / 12832 := by
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
    (completeRAData (tableEnvelope C) 12832 164).locationBound 12832 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12832 164).energyBound 12832 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12832 164) (d.f1 12832 164) d.f2 ≤
      32 * (((2232873993 / 500000000000000000) : ℝ) + (1489849283 / 1000000000000000000) + (179042939 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12832 164) (d.w1 12832 164)
      (d.w2 12832 164) ≤
      32 * (((222150351 / 12500000000000000000) : ℝ) + (316111481 / 25000000000000000000) + (57749571 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12832 164) (d.f1 12832 164) d.f2 ≤
      ((2232873993 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2232873993 / 500000000000000000)) * ((1489849283 / 1000000000000000000)) * (126 / 100) +
      2 * (((1489849283 / 1000000000000000000)) ^ 2 + 2 * ((2232873993 / 500000000000000000)) * ((179042939 / 500000000000000000))) +
      6 * ((1489849283 / 1000000000000000000)) * ((179042939 / 500000000000000000)) * (126 / 100) + 8 * ((179042939 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12832 164) (d.f1 12832 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12832 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12832 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12832 164) (d.f1 12832 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12832 164) (d.w1 12832 164) (d.w2 12832 164)
  have hwexpr0 : 0 ≤ d.w0 12832 164 + d.w1 12832 164 * √(π / 2) +
      2 * d.w2 12832 164 + energyR16 12832 *
      radiusPolynomialRoot16 (d.w0 12832 164) (d.w1 12832 164) (d.w2 12832 164) := by
    positivity
  constructor
  · change (12832 : ℝ) ^ 8 * (mA 12832 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12832 164) (d.f1 12832 164) d.f2 + locationR16 12832 *
        radiusPolynomialRoot16 (d.f0 12832 164) (d.f1 12832 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12832 : ℝ) ^ 8 * (mA 12832 : ℝ) ^ 8 *
        ((((2232873993 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2232873993 / 500000000000000000)) * ((1489849283 / 1000000000000000000)) * (126 / 100) +
          2 * (((1489849283 / 1000000000000000000)) ^ 2 + 2 * ((2232873993 / 500000000000000000)) * ((179042939 / 500000000000000000))) +
          6 * ((1489849283 / 1000000000000000000)) * ((179042939 / 500000000000000000)) * (126 / 100) + 8 * ((179042939 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12832) *
          (32 * (((2232873993 / 500000000000000000) : ℝ) + (1489849283 / 1000000000000000000) + (179042939 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12832 : ℝ) ^ 16 *
      (d.w0 12832 164 + d.w1 12832 164 * √(π / 2) + 2 * d.w2 12832 164 +
        energyR16 12832 * radiusPolynomialRoot16 (d.w0 12832 164) (d.w1 12832 164)
          (d.w2 12832 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12832 : ℝ) ^ 16 *
        (((222150351 / 12500000000000000000) : ℝ) + ((316111481 / 25000000000000000000)) * (126 / 100) + 2 * ((57749571 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12832) *
          (32 * (((222150351 / 12500000000000000000) : ℝ) + (316111481 / 25000000000000000000) + (57749571 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12832

/-! A coarse bound on the actual paper statistics constant at dimension 12833. -/
namespace BstLean.Part266.Row12833
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12831 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12831 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12831 128 ≤ (13085 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13085 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12833) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12833 : ℕ))
    (by norm_num : (12833 : ℕ) ≤ 16384)
  have ht : paperTail256 12833 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12833 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12833 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12833 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12833 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12833 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12831 128 * √(2 / (12833 : ℝ)) *
      (√(12833 : ℝ) + paperT0 12833 + paperTail256 12833) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12833 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12833 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12833 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12831 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12831 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12833 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12833

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12833
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12833 (61 / 100) 164 (17 / (100 * 12833)) (26 / (10 * 12833)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12833 (61 / 100) 164 (17 / (100 * 12833)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (461884007 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1439675877 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (470661401 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12833 / 12833 * (61 / 100)) ^ 4 * inverseRadius8 (12833 - 1) /
            envelopeGap 12833 (61 / 100) 164 (17 / (100 * 12833)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12833

namespace BstLean.Part266.Row12833
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12833 164 ≤ (4464878657 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12833 164 ≤ (1489559193 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (358016137 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12833 164 ≤ (177678749 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 12833 164 ≤ (632075201 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12833 164 ≤ (461888567 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (461884007 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (461884007 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1439675877 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (470661401 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((454957 / 125000000) : ℝ) ≤ √(17 / (100 * 12833) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12833) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (429829737 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37943060987 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12833) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12833) ≤ (55100661 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12833) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12833 * (164 : ℝ) ^ 2 + 26 / (10 * 12833) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12833) : ℝ)) (tA 12833 * 164 ^ 2 + 26 / (10 * 12833)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((454957 / 125000000))) * ((461884007 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((454957 / 125000000)) ^ 3) * ((1439675877 / 1000000000000000000000000))) + ((470661401 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((454957 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12833) : ℝ)) d.D d.V d.P (√(tA 12833) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((454957 / 125000000)) ^ 2 * (((429829737 / 200000000000000)) * ((37943060987 / 1000000000000000000)))) + ((470661401 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12833) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((454957 / 125000000)) * ((461884007 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12833) : ℝ)) (tA 12833 * 164 ^ 2 + 26 / (10 * 12833)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((461884007 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((454957 / 125000000)) ^ 2) * ((1439675877 / 1000000000000000000000000)) + ((470661401 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12833) : ℝ)) (√(26 / (10 * 12833) : ℝ)) d.D d.V d.P (√(tA 12833) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((454957 / 125000000)) * (((429829737 / 200000000000000)) * ((37943060987 / 1000000000000000000))) + ((470661401 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12833) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((461884007 / 100000000000000000000) : ℝ) + ((470661401 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12833

namespace BstLean.Part266.Row12833
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12833 164 ∧
    0 ≤ (tableEnvelope C).f1 12833 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12833 164 ∧
    0 ≤ (tableEnvelope C).w1 12833 164 ∧ 0 ≤ (tableEnvelope C).w2 12833 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12833 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12833 164 ∧ 0 ≤ d.f1 12833 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12833 164 ∧ 0 ≤ d.w1 12833 164 ∧ 0 ≤ d.w2 12833 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12833 ≤ 2 * (228 / 100 : ℝ) / 12833 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12833 ≤ 2 * (370 / 100 : ℝ) / 12833 := by
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
    (completeRAData (tableEnvelope C) 12833 164).locationBound 12833 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12833 164).energyBound 12833 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12833 164) (d.f1 12833 164) d.f2 ≤
      32 * (((4464878657 / 1000000000000000000) : ℝ) + (1489559193 / 1000000000000000000) + (358016137 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12833 164) (d.w1 12833 164)
      (d.w2 12833 164) ≤
      32 * (((177678749 / 10000000000000000000) : ℝ) + (632075201 / 50000000000000000000) + (461888567 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12833 164) (d.f1 12833 164) d.f2 ≤
      ((4464878657 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4464878657 / 1000000000000000000)) * ((1489559193 / 1000000000000000000)) * (126 / 100) +
      2 * (((1489559193 / 1000000000000000000)) ^ 2 + 2 * ((4464878657 / 1000000000000000000)) * ((358016137 / 1000000000000000000))) +
      6 * ((1489559193 / 1000000000000000000)) * ((358016137 / 1000000000000000000)) * (126 / 100) + 8 * ((358016137 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12833 164) (d.f1 12833 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12833 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12833 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12833 164) (d.f1 12833 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12833 164) (d.w1 12833 164) (d.w2 12833 164)
  have hwexpr0 : 0 ≤ d.w0 12833 164 + d.w1 12833 164 * √(π / 2) +
      2 * d.w2 12833 164 + energyR16 12833 *
      radiusPolynomialRoot16 (d.w0 12833 164) (d.w1 12833 164) (d.w2 12833 164) := by
    positivity
  constructor
  · change (12833 : ℝ) ^ 8 * (mA 12833 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12833 164) (d.f1 12833 164) d.f2 + locationR16 12833 *
        radiusPolynomialRoot16 (d.f0 12833 164) (d.f1 12833 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12833 : ℝ) ^ 8 * (mA 12833 : ℝ) ^ 8 *
        ((((4464878657 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4464878657 / 1000000000000000000)) * ((1489559193 / 1000000000000000000)) * (126 / 100) +
          2 * (((1489559193 / 1000000000000000000)) ^ 2 + 2 * ((4464878657 / 1000000000000000000)) * ((358016137 / 1000000000000000000))) +
          6 * ((1489559193 / 1000000000000000000)) * ((358016137 / 1000000000000000000)) * (126 / 100) + 8 * ((358016137 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12833) *
          (32 * (((4464878657 / 1000000000000000000) : ℝ) + (1489559193 / 1000000000000000000) + (358016137 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12833 : ℝ) ^ 16 *
      (d.w0 12833 164 + d.w1 12833 164 * √(π / 2) + 2 * d.w2 12833 164 +
        energyR16 12833 * radiusPolynomialRoot16 (d.w0 12833 164) (d.w1 12833 164)
          (d.w2 12833 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12833 : ℝ) ^ 16 *
        (((177678749 / 10000000000000000000) : ℝ) + ((632075201 / 50000000000000000000)) * (126 / 100) + 2 * ((461888567 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12833) *
          (32 * (((177678749 / 10000000000000000000) : ℝ) + (632075201 / 50000000000000000000) + (461888567 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12833

/-! A coarse bound on the actual paper statistics constant at dimension 12834. -/
namespace BstLean.Part266.Row12834
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12832 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12832 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12832 128 ≤ (13086 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13086 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12834) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12834 : ℕ))
    (by norm_num : (12834 : ℕ) ≤ 16384)
  have ht : paperTail256 12834 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12834 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12834 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12834 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12834 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12834 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12832 128 * √(2 / (12834 : ℝ)) *
      (√(12834 : ℝ) + paperT0 12834 + paperTail256 12834) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12834 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12834 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12834 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12832 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12832 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12834 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12834

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12834
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12834 (61 / 100) 164 (17 / (100 * 12834)) (26 / (10 * 12834)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12834 (61 / 100) 164 (17 / (100 * 12834)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (230888021 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (287845441 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4703652657 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12834 / 12834 * (61 / 100)) ^ 4 * inverseRadius8 (12834 - 1) /
            envelopeGap 12834 (61 / 100) 164 (17 / (100 * 12834)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12834

namespace BstLean.Part266.Row12834
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12834 164 ≤ (558001203 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12834 164 ≤ (372317299 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (22371651 / 62500000000000000)
  w0 : (tableEnvelope C).w0 12834 164 ≤ (1776372313 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12834 164 ≤ (631927489 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12834 164 ≤ (461780599 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (230888021 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (230888021 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (287845441 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4703652657 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1819757 / 500000000) : ℝ) ≤ √(17 / (100 * 12834) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12834) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (214889749 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4742143511 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12834) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12834) ≤ (3443523 / 31250000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12834) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12834 * (164 : ℝ) ^ 2 + 26 / (10 * 12834) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12834) : ℝ)) (tA 12834 * 164 ^ 2 + 26 / (10 * 12834)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1819757 / 500000000))) * ((230888021 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1819757 / 500000000)) ^ 3) * ((287845441 / 200000000000000000000000))) + ((4703652657 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1819757 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12834) : ℝ)) d.D d.V d.P (√(tA 12834) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1819757 / 500000000)) ^ 2 * (((214889749 / 100000000000000)) * ((4742143511 / 125000000000000000)))) + ((4703652657 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12834) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1819757 / 500000000)) * ((230888021 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12834) : ℝ)) (tA 12834 * 164 ^ 2 + 26 / (10 * 12834)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((230888021 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1819757 / 500000000)) ^ 2) * ((287845441 / 200000000000000000000000)) + ((4703652657 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12834) : ℝ)) (√(26 / (10 * 12834) : ℝ)) d.D d.V d.P (√(tA 12834) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1819757 / 500000000)) * (((214889749 / 100000000000000)) * ((4742143511 / 125000000000000000))) + ((4703652657 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12834) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((230888021 / 50000000000000000000) : ℝ) + ((4703652657 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12834

namespace BstLean.Part266.Row12834
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12834 164 ∧
    0 ≤ (tableEnvelope C).f1 12834 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12834 164 ∧
    0 ≤ (tableEnvelope C).w1 12834 164 ∧ 0 ≤ (tableEnvelope C).w2 12834 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12834 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12834 164 ∧ 0 ≤ d.f1 12834 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12834 164 ∧ 0 ≤ d.w1 12834 164 ∧ 0 ≤ d.w2 12834 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12834 ≤ 2 * (228 / 100 : ℝ) / 12834 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12834 ≤ 2 * (370 / 100 : ℝ) / 12834 := by
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
    (completeRAData (tableEnvelope C) 12834 164).locationBound 12834 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12834 164).energyBound 12834 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12834 164) (d.f1 12834 164) d.f2 ≤
      32 * (((558001203 / 125000000000000000) : ℝ) + (372317299 / 250000000000000000) + (22371651 / 62500000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12834 164) (d.w1 12834 164)
      (d.w2 12834 164) ≤
      32 * (((1776372313 / 100000000000000000000) : ℝ) + (631927489 / 50000000000000000000) + (461780599 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12834 164) (d.f1 12834 164) d.f2 ≤
      ((558001203 / 125000000000000000) : ℝ) ^ 2 + 2 * ((558001203 / 125000000000000000)) * ((372317299 / 250000000000000000)) * (126 / 100) +
      2 * (((372317299 / 250000000000000000)) ^ 2 + 2 * ((558001203 / 125000000000000000)) * ((22371651 / 62500000000000000))) +
      6 * ((372317299 / 250000000000000000)) * ((22371651 / 62500000000000000)) * (126 / 100) + 8 * ((22371651 / 62500000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12834 164) (d.f1 12834 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12834 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12834 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12834 164) (d.f1 12834 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12834 164) (d.w1 12834 164) (d.w2 12834 164)
  have hwexpr0 : 0 ≤ d.w0 12834 164 + d.w1 12834 164 * √(π / 2) +
      2 * d.w2 12834 164 + energyR16 12834 *
      radiusPolynomialRoot16 (d.w0 12834 164) (d.w1 12834 164) (d.w2 12834 164) := by
    positivity
  constructor
  · change (12834 : ℝ) ^ 8 * (mA 12834 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12834 164) (d.f1 12834 164) d.f2 + locationR16 12834 *
        radiusPolynomialRoot16 (d.f0 12834 164) (d.f1 12834 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12834 : ℝ) ^ 8 * (mA 12834 : ℝ) ^ 8 *
        ((((558001203 / 125000000000000000) : ℝ) ^ 2 + 2 * ((558001203 / 125000000000000000)) * ((372317299 / 250000000000000000)) * (126 / 100) +
          2 * (((372317299 / 250000000000000000)) ^ 2 + 2 * ((558001203 / 125000000000000000)) * ((22371651 / 62500000000000000))) +
          6 * ((372317299 / 250000000000000000)) * ((22371651 / 62500000000000000)) * (126 / 100) + 8 * ((22371651 / 62500000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12834) *
          (32 * (((558001203 / 125000000000000000) : ℝ) + (372317299 / 250000000000000000) + (22371651 / 62500000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12834 : ℝ) ^ 16 *
      (d.w0 12834 164 + d.w1 12834 164 * √(π / 2) + 2 * d.w2 12834 164 +
        energyR16 12834 * radiusPolynomialRoot16 (d.w0 12834 164) (d.w1 12834 164)
          (d.w2 12834 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12834 : ℝ) ^ 16 *
        (((1776372313 / 100000000000000000000) : ℝ) + ((631927489 / 50000000000000000000)) * (126 / 100) + 2 * ((461780599 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12834) *
          (32 * (((1776372313 / 100000000000000000000) : ℝ) + (631927489 / 50000000000000000000) + (461780599 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12834

/-! A coarse bound on the actual paper statistics constant at dimension 12835. -/
namespace BstLean.Part266.Row12835
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12833 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12833 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12833 128 ≤ (13087 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13087 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12835) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12835 : ℕ))
    (by norm_num : (12835 : ℕ) ≤ 16384)
  have ht : paperTail256 12835 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12835 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12835 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12835 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12835 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12835 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12833 128 * √(2 / (12835 : ℝ)) *
      (√(12835 : ℝ) + paperT0 12835 + paperTail256 12835) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12835 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12835 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12835 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12833 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12833 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12835 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12835

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12835
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12835 (61 / 100) 164 (17 / (100 * 12835)) (26 / (10 * 12835)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12835 (61 / 100) 164 (17 / (100 * 12835)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (28854257 / 6250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (359694677 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2350346701 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12835 / 12835 * (61 / 100)) ^ 4 * inverseRadius8 (12835 - 1) /
            envelopeGap 12835 (61 / 100) 164 (17 / (100 * 12835)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12835

namespace BstLean.Part266.Row12835
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12835 164 ≤ (557892611 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12835 164 ≤ (1488979293 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (357876717 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12835 164 ≤ (1775957279 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12835 164 ≤ (1263559653 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12835 164 ≤ (230836333 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (28854257 / 6250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (28854257 / 6250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (359694677 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2350346701 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((909843 / 250000000) : ℝ) ≤ √(17 / (100 * 12835) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12835) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1074323173 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18965618287 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12835) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12835) ≤ (2203683 / 20000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12835) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12835 * (164 : ℝ) ^ 2 + 26 / (10 * 12835) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12835) : ℝ)) (tA 12835 * 164 ^ 2 + 26 / (10 * 12835)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((909843 / 250000000))) * ((28854257 / 6250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((909843 / 250000000)) ^ 3) * ((359694677 / 250000000000000000000000))) + ((2350346701 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((909843 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12835) : ℝ)) d.D d.V d.P (√(tA 12835) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((909843 / 250000000)) ^ 2 * (((1074323173 / 500000000000000)) * ((18965618287 / 500000000000000000)))) + ((2350346701 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12835) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((909843 / 250000000)) * ((28854257 / 6250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12835) : ℝ)) (tA 12835 * 164 ^ 2 + 26 / (10 * 12835)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((28854257 / 6250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((909843 / 250000000)) ^ 2) * ((359694677 / 250000000000000000000000)) + ((2350346701 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12835) : ℝ)) (√(26 / (10 * 12835) : ℝ)) d.D d.V d.P (√(tA 12835) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((909843 / 250000000)) * (((1074323173 / 500000000000000)) * ((18965618287 / 500000000000000000))) + ((2350346701 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12835) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((28854257 / 6250000000000000000) : ℝ) + ((2350346701 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12835

namespace BstLean.Part266.Row12835
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12835 164 ∧
    0 ≤ (tableEnvelope C).f1 12835 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12835 164 ∧
    0 ≤ (tableEnvelope C).w1 12835 164 ∧ 0 ≤ (tableEnvelope C).w2 12835 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12835 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12835 164 ∧ 0 ≤ d.f1 12835 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12835 164 ∧ 0 ≤ d.w1 12835 164 ∧ 0 ≤ d.w2 12835 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12835 ≤ 2 * (228 / 100 : ℝ) / 12835 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12835 ≤ 2 * (370 / 100 : ℝ) / 12835 := by
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
    (completeRAData (tableEnvelope C) 12835 164).locationBound 12835 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12835 164).energyBound 12835 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12835 164) (d.f1 12835 164) d.f2 ≤
      32 * (((557892611 / 125000000000000000) : ℝ) + (1488979293 / 1000000000000000000) + (357876717 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12835 164) (d.w1 12835 164)
      (d.w2 12835 164) ≤
      32 * (((1775957279 / 100000000000000000000) : ℝ) + (1263559653 / 100000000000000000000) + (230836333 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12835 164) (d.f1 12835 164) d.f2 ≤
      ((557892611 / 125000000000000000) : ℝ) ^ 2 + 2 * ((557892611 / 125000000000000000)) * ((1488979293 / 1000000000000000000)) * (126 / 100) +
      2 * (((1488979293 / 1000000000000000000)) ^ 2 + 2 * ((557892611 / 125000000000000000)) * ((357876717 / 1000000000000000000))) +
      6 * ((1488979293 / 1000000000000000000)) * ((357876717 / 1000000000000000000)) * (126 / 100) + 8 * ((357876717 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12835 164) (d.f1 12835 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12835 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12835 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12835 164) (d.f1 12835 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12835 164) (d.w1 12835 164) (d.w2 12835 164)
  have hwexpr0 : 0 ≤ d.w0 12835 164 + d.w1 12835 164 * √(π / 2) +
      2 * d.w2 12835 164 + energyR16 12835 *
      radiusPolynomialRoot16 (d.w0 12835 164) (d.w1 12835 164) (d.w2 12835 164) := by
    positivity
  constructor
  · change (12835 : ℝ) ^ 8 * (mA 12835 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12835 164) (d.f1 12835 164) d.f2 + locationR16 12835 *
        radiusPolynomialRoot16 (d.f0 12835 164) (d.f1 12835 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12835 : ℝ) ^ 8 * (mA 12835 : ℝ) ^ 8 *
        ((((557892611 / 125000000000000000) : ℝ) ^ 2 + 2 * ((557892611 / 125000000000000000)) * ((1488979293 / 1000000000000000000)) * (126 / 100) +
          2 * (((1488979293 / 1000000000000000000)) ^ 2 + 2 * ((557892611 / 125000000000000000)) * ((357876717 / 1000000000000000000))) +
          6 * ((1488979293 / 1000000000000000000)) * ((357876717 / 1000000000000000000)) * (126 / 100) + 8 * ((357876717 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12835) *
          (32 * (((557892611 / 125000000000000000) : ℝ) + (1488979293 / 1000000000000000000) + (357876717 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12835 : ℝ) ^ 16 *
      (d.w0 12835 164 + d.w1 12835 164 * √(π / 2) + 2 * d.w2 12835 164 +
        energyR16 12835 * radiusPolynomialRoot16 (d.w0 12835 164) (d.w1 12835 164)
          (d.w2 12835 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12835 : ℝ) ^ 16 *
        (((1775957279 / 100000000000000000000) : ℝ) + ((1263559653 / 100000000000000000000)) * (126 / 100) + 2 * ((230836333 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12835) *
          (32 * (((1775957279 / 100000000000000000000) : ℝ) + (1263559653 / 100000000000000000000) + (230836333 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12835

/-! A coarse bound on the actual paper statistics constant at dimension 12836. -/
namespace BstLean.Part266.Row12836
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12834 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12834 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12834 128 ≤ (13088 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13088 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12836) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12836 : ℕ))
    (by norm_num : (12836 : ℕ) ≤ 16384)
  have ht : paperTail256 12836 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12836 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12836 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12836 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12836 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12836 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12834 128 * √(2 / (12836 : ℝ)) *
      (√(12836 : ℝ) + paperT0 12836 + paperTail256 12836) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12836 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12836 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12836 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12834 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12834 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12836 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12836

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12836
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12836 (61 / 100) 164 (17 / (100 * 12836)) (26 / (10 * 12836)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12836 (61 / 100) 164 (17 / (100 * 12836)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (230780107 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (719165193 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1174434061 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12836 / 12836 * (61 / 100)) ^ 4 * inverseRadius8 (12836 - 1) /
            envelopeGap 12836 (61 / 100) 164 (17 / (100 * 12836)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12836

namespace BstLean.Part266.Row12836
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12836 164 ≤ (4462272447 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12836 164 ≤ (1488689481 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (357807037 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12836 164 ≤ (110971399 / 6250000000000000000)
  w1 : (tableEnvelope C).w1 12836 164 ≤ (50530577 / 4000000000000000000)
  w2 : (tableEnvelope C).w2 12836 164 ≤ (92312953 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (230780107 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (230780107 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (719165193 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1174434061 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((363923 / 100000000) : ℝ) ≤ √(17 / (100 * 12836) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12836) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (134274703 / 62500000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18962663223 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12836) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12836) ≤ (55087783 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12836) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12836 * (164 : ℝ) ^ 2 + 26 / (10 * 12836) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12836) : ℝ)) (tA 12836 * 164 ^ 2 + 26 / (10 * 12836)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((363923 / 100000000))) * ((230780107 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((363923 / 100000000)) ^ 3) * ((719165193 / 500000000000000000000000))) + ((1174434061 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((363923 / 100000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12836) : ℝ)) d.D d.V d.P (√(tA 12836) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((363923 / 100000000)) ^ 2 * (((134274703 / 62500000000000)) * ((18962663223 / 500000000000000000)))) + ((1174434061 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12836) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((363923 / 100000000)) * ((230780107 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12836) : ℝ)) (tA 12836 * 164 ^ 2 + 26 / (10 * 12836)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((230780107 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((363923 / 100000000)) ^ 2) * ((719165193 / 500000000000000000000000)) + ((1174434061 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12836) : ℝ)) (√(26 / (10 * 12836) : ℝ)) d.D d.V d.P (√(tA 12836) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((363923 / 100000000)) * (((134274703 / 62500000000000)) * ((18962663223 / 500000000000000000))) + ((1174434061 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12836) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((230780107 / 50000000000000000000) : ℝ) + ((1174434061 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12836

namespace BstLean.Part266.Row12836
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12836 164 ∧
    0 ≤ (tableEnvelope C).f1 12836 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12836 164 ∧
    0 ≤ (tableEnvelope C).w1 12836 164 ∧ 0 ≤ (tableEnvelope C).w2 12836 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12836 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12836 164 ∧ 0 ≤ d.f1 12836 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12836 164 ∧ 0 ≤ d.w1 12836 164 ∧ 0 ≤ d.w2 12836 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12836 ≤ 2 * (228 / 100 : ℝ) / 12836 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12836 ≤ 2 * (370 / 100 : ℝ) / 12836 := by
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
    (completeRAData (tableEnvelope C) 12836 164).locationBound 12836 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12836 164).energyBound 12836 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12836 164) (d.f1 12836 164) d.f2 ≤
      32 * (((4462272447 / 1000000000000000000) : ℝ) + (1488689481 / 1000000000000000000) + (357807037 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12836 164) (d.w1 12836 164)
      (d.w2 12836 164) ≤
      32 * (((110971399 / 6250000000000000000) : ℝ) + (50530577 / 4000000000000000000) + (92312953 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12836 164) (d.f1 12836 164) d.f2 ≤
      ((4462272447 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4462272447 / 1000000000000000000)) * ((1488689481 / 1000000000000000000)) * (126 / 100) +
      2 * (((1488689481 / 1000000000000000000)) ^ 2 + 2 * ((4462272447 / 1000000000000000000)) * ((357807037 / 1000000000000000000))) +
      6 * ((1488689481 / 1000000000000000000)) * ((357807037 / 1000000000000000000)) * (126 / 100) + 8 * ((357807037 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12836 164) (d.f1 12836 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12836 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12836 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12836 164) (d.f1 12836 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12836 164) (d.w1 12836 164) (d.w2 12836 164)
  have hwexpr0 : 0 ≤ d.w0 12836 164 + d.w1 12836 164 * √(π / 2) +
      2 * d.w2 12836 164 + energyR16 12836 *
      radiusPolynomialRoot16 (d.w0 12836 164) (d.w1 12836 164) (d.w2 12836 164) := by
    positivity
  constructor
  · change (12836 : ℝ) ^ 8 * (mA 12836 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12836 164) (d.f1 12836 164) d.f2 + locationR16 12836 *
        radiusPolynomialRoot16 (d.f0 12836 164) (d.f1 12836 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12836 : ℝ) ^ 8 * (mA 12836 : ℝ) ^ 8 *
        ((((4462272447 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4462272447 / 1000000000000000000)) * ((1488689481 / 1000000000000000000)) * (126 / 100) +
          2 * (((1488689481 / 1000000000000000000)) ^ 2 + 2 * ((4462272447 / 1000000000000000000)) * ((357807037 / 1000000000000000000))) +
          6 * ((1488689481 / 1000000000000000000)) * ((357807037 / 1000000000000000000)) * (126 / 100) + 8 * ((357807037 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12836) *
          (32 * (((4462272447 / 1000000000000000000) : ℝ) + (1488689481 / 1000000000000000000) + (357807037 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12836 : ℝ) ^ 16 *
      (d.w0 12836 164 + d.w1 12836 164 * √(π / 2) + 2 * d.w2 12836 164 +
        energyR16 12836 * radiusPolynomialRoot16 (d.w0 12836 164) (d.w1 12836 164)
          (d.w2 12836 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12836 : ℝ) ^ 16 *
        (((110971399 / 6250000000000000000) : ℝ) + ((50530577 / 4000000000000000000)) * (126 / 100) + 2 * ((92312953 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12836) *
          (32 * (((110971399 / 6250000000000000000) : ℝ) + (50530577 / 4000000000000000000) + (92312953 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12836

/-! A coarse bound on the actual paper statistics constant at dimension 12837. -/
namespace BstLean.Part266.Row12837
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12835 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12835 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12835 128 ≤ (13089 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13089 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12837) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12837 : ℕ))
    (by norm_num : (12837 : ℕ) ≤ 16384)
  have ht : paperTail256 12837 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12837 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12837 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12837 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12837 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12837 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12835 128 * √(2 / (12837 : ℝ)) *
      (√(12837 : ℝ) + paperT0 12837 + paperTail256 12837) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12837 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12837 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12837 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12835 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12835 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12837 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12837

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12837
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12837 (61 / 100) 164 (17 / (100 * 12837)) (26 / (10 * 12837)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12837 (61 / 100) 164 (17 / (100 * 12837)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (461452351 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (718941119 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4694781181 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12837 / 12837 * (61 / 100)) ^ 4 * inverseRadius8 (12837 - 1) /
            envelopeGap 12837 (61 / 100) 164 (17 / (100 * 12837)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12837

namespace BstLean.Part266.Row12837
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12837 164 ≤ (2230700381 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12837 164 ≤ (297679789 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (357737281 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12837 164 ≤ (177512691 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 12837 164 ≤ (315742237 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12837 164 ≤ (461456899 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (461452351 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (461452351 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (718941119 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4694781181 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3639089 / 1000000000) : ℝ) ≤ √(17 / (100 * 12837) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12837) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1074072101 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37919417691 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12837) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12837) ≤ (13770873 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12837) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12837 * (164 : ℝ) ^ 2 + 26 / (10 * 12837) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12837) : ℝ)) (tA 12837 * 164 ^ 2 + 26 / (10 * 12837)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3639089 / 1000000000))) * ((461452351 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3639089 / 1000000000)) ^ 3) * ((718941119 / 500000000000000000000000))) + ((4694781181 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3639089 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12837) : ℝ)) d.D d.V d.P (√(tA 12837) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3639089 / 1000000000)) ^ 2 * (((1074072101 / 500000000000000)) * ((37919417691 / 1000000000000000000)))) + ((4694781181 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12837) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3639089 / 1000000000)) * ((461452351 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12837) : ℝ)) (tA 12837 * 164 ^ 2 + 26 / (10 * 12837)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((461452351 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3639089 / 1000000000)) ^ 2) * ((718941119 / 500000000000000000000000)) + ((4694781181 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12837) : ℝ)) (√(26 / (10 * 12837) : ℝ)) d.D d.V d.P (√(tA 12837) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3639089 / 1000000000)) * (((1074072101 / 500000000000000)) * ((37919417691 / 1000000000000000000))) + ((4694781181 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12837) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((461452351 / 100000000000000000000) : ℝ) + ((4694781181 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12837

namespace BstLean.Part266.Row12837
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12837 164 ∧
    0 ≤ (tableEnvelope C).f1 12837 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12837 164 ∧
    0 ≤ (tableEnvelope C).w1 12837 164 ∧ 0 ≤ (tableEnvelope C).w2 12837 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12837 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12837 164 ∧ 0 ≤ d.f1 12837 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12837 164 ∧ 0 ≤ d.w1 12837 164 ∧ 0 ≤ d.w2 12837 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12837 ≤ 2 * (228 / 100 : ℝ) / 12837 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12837 ≤ 2 * (370 / 100 : ℝ) / 12837 := by
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
    (completeRAData (tableEnvelope C) 12837 164).locationBound 12837 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12837 164).energyBound 12837 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12837 164) (d.f1 12837 164) d.f2 ≤
      32 * (((2230700381 / 500000000000000000) : ℝ) + (297679789 / 200000000000000000) + (357737281 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12837 164) (d.w1 12837 164)
      (d.w2 12837 164) ≤
      32 * (((177512691 / 10000000000000000000) : ℝ) + (315742237 / 25000000000000000000) + (461456899 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12837 164) (d.f1 12837 164) d.f2 ≤
      ((2230700381 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2230700381 / 500000000000000000)) * ((297679789 / 200000000000000000)) * (126 / 100) +
      2 * (((297679789 / 200000000000000000)) ^ 2 + 2 * ((2230700381 / 500000000000000000)) * ((357737281 / 1000000000000000000))) +
      6 * ((297679789 / 200000000000000000)) * ((357737281 / 1000000000000000000)) * (126 / 100) + 8 * ((357737281 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12837 164) (d.f1 12837 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12837 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12837 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12837 164) (d.f1 12837 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12837 164) (d.w1 12837 164) (d.w2 12837 164)
  have hwexpr0 : 0 ≤ d.w0 12837 164 + d.w1 12837 164 * √(π / 2) +
      2 * d.w2 12837 164 + energyR16 12837 *
      radiusPolynomialRoot16 (d.w0 12837 164) (d.w1 12837 164) (d.w2 12837 164) := by
    positivity
  constructor
  · change (12837 : ℝ) ^ 8 * (mA 12837 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12837 164) (d.f1 12837 164) d.f2 + locationR16 12837 *
        radiusPolynomialRoot16 (d.f0 12837 164) (d.f1 12837 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12837 : ℝ) ^ 8 * (mA 12837 : ℝ) ^ 8 *
        ((((2230700381 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2230700381 / 500000000000000000)) * ((297679789 / 200000000000000000)) * (126 / 100) +
          2 * (((297679789 / 200000000000000000)) ^ 2 + 2 * ((2230700381 / 500000000000000000)) * ((357737281 / 1000000000000000000))) +
          6 * ((297679789 / 200000000000000000)) * ((357737281 / 1000000000000000000)) * (126 / 100) + 8 * ((357737281 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12837) *
          (32 * (((2230700381 / 500000000000000000) : ℝ) + (297679789 / 200000000000000000) + (357737281 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12837 : ℝ) ^ 16 *
      (d.w0 12837 164 + d.w1 12837 164 * √(π / 2) + 2 * d.w2 12837 164 +
        energyR16 12837 * radiusPolynomialRoot16 (d.w0 12837 164) (d.w1 12837 164)
          (d.w2 12837 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12837 : ℝ) ^ 16 *
        (((177512691 / 10000000000000000000) : ℝ) + ((315742237 / 25000000000000000000)) * (126 / 100) + 2 * ((461456899 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12837) *
          (32 * (((177512691 / 10000000000000000000) : ℝ) + (315742237 / 25000000000000000000) + (461456899 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12837

/-! A coarse bound on the actual paper statistics constant at dimension 12838. -/
namespace BstLean.Part266.Row12838
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12836 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12836 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12836 128 ≤ (13090 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13090 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12838) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12838 : ℕ))
    (by norm_num : (12838 : ℕ) ≤ 16384)
  have ht : paperTail256 12838 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12838 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12838 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12838 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12838 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12838 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12836 128 * √(2 / (12838 : ℝ)) *
      (√(12838 : ℝ) + paperT0 12838 + paperTail256 12838) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12838 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12838 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12838 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12836 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12836 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12838 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12838

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12838
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12838 (61 / 100) 164 (17 / (100 * 12838)) (26 / (10 * 12838)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12838 (61 / 100) 164 (17 / (100 * 12838)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (461344521 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (287486853 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4691828211 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12838 / 12838 * (61 / 100)) ^ 4 * inverseRadius8 (12838 - 1) /
            envelopeGap 12838 (61 / 100) 164 (17 / (100 * 12838)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12838

namespace BstLean.Part266.Row12838
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12838 164 ≤ (4460532913 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12838 164 ≤ (1488109319 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (357667643 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12838 164 ≤ (1774712299 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12838 164 ≤ (315668479 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12838 164 ≤ (230674533 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (461344521 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (461344521 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (287486853 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4691828211 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3638947 / 1000000000) : ℝ) ≤ √(17 / (100 * 12838) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12838) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2147893203 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37913510323 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12838) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12838) ≤ (55079201 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12838) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12838 * (164 : ℝ) ^ 2 + 26 / (10 * 12838) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12838) : ℝ)) (tA 12838 * 164 ^ 2 + 26 / (10 * 12838)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3638947 / 1000000000))) * ((461344521 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3638947 / 1000000000)) ^ 3) * ((287486853 / 200000000000000000000000))) + ((4691828211 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3638947 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12838) : ℝ)) d.D d.V d.P (√(tA 12838) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3638947 / 1000000000)) ^ 2 * (((2147893203 / 1000000000000000)) * ((37913510323 / 1000000000000000000)))) + ((4691828211 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12838) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3638947 / 1000000000)) * ((461344521 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12838) : ℝ)) (tA 12838 * 164 ^ 2 + 26 / (10 * 12838)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((461344521 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3638947 / 1000000000)) ^ 2) * ((287486853 / 200000000000000000000000)) + ((4691828211 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12838) : ℝ)) (√(26 / (10 * 12838) : ℝ)) d.D d.V d.P (√(tA 12838) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3638947 / 1000000000)) * (((2147893203 / 1000000000000000)) * ((37913510323 / 1000000000000000000))) + ((4691828211 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12838) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((461344521 / 100000000000000000000) : ℝ) + ((4691828211 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12838

namespace BstLean.Part266.Row12838
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12838 164 ∧
    0 ≤ (tableEnvelope C).f1 12838 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12838 164 ∧
    0 ≤ (tableEnvelope C).w1 12838 164 ∧ 0 ≤ (tableEnvelope C).w2 12838 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12838 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12838 164 ∧ 0 ≤ d.f1 12838 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12838 164 ∧ 0 ≤ d.w1 12838 164 ∧ 0 ≤ d.w2 12838 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12838 ≤ 2 * (228 / 100 : ℝ) / 12838 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12838 ≤ 2 * (370 / 100 : ℝ) / 12838 := by
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
    (completeRAData (tableEnvelope C) 12838 164).locationBound 12838 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12838 164).energyBound 12838 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12838 164) (d.f1 12838 164) d.f2 ≤
      32 * (((4460532913 / 1000000000000000000) : ℝ) + (1488109319 / 1000000000000000000) + (357667643 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12838 164) (d.w1 12838 164)
      (d.w2 12838 164) ≤
      32 * (((1774712299 / 100000000000000000000) : ℝ) + (315668479 / 25000000000000000000) + (230674533 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12838 164) (d.f1 12838 164) d.f2 ≤
      ((4460532913 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4460532913 / 1000000000000000000)) * ((1488109319 / 1000000000000000000)) * (126 / 100) +
      2 * (((1488109319 / 1000000000000000000)) ^ 2 + 2 * ((4460532913 / 1000000000000000000)) * ((357667643 / 1000000000000000000))) +
      6 * ((1488109319 / 1000000000000000000)) * ((357667643 / 1000000000000000000)) * (126 / 100) + 8 * ((357667643 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12838 164) (d.f1 12838 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12838 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12838 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12838 164) (d.f1 12838 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12838 164) (d.w1 12838 164) (d.w2 12838 164)
  have hwexpr0 : 0 ≤ d.w0 12838 164 + d.w1 12838 164 * √(π / 2) +
      2 * d.w2 12838 164 + energyR16 12838 *
      radiusPolynomialRoot16 (d.w0 12838 164) (d.w1 12838 164) (d.w2 12838 164) := by
    positivity
  constructor
  · change (12838 : ℝ) ^ 8 * (mA 12838 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12838 164) (d.f1 12838 164) d.f2 + locationR16 12838 *
        radiusPolynomialRoot16 (d.f0 12838 164) (d.f1 12838 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12838 : ℝ) ^ 8 * (mA 12838 : ℝ) ^ 8 *
        ((((4460532913 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4460532913 / 1000000000000000000)) * ((1488109319 / 1000000000000000000)) * (126 / 100) +
          2 * (((1488109319 / 1000000000000000000)) ^ 2 + 2 * ((4460532913 / 1000000000000000000)) * ((357667643 / 1000000000000000000))) +
          6 * ((1488109319 / 1000000000000000000)) * ((357667643 / 1000000000000000000)) * (126 / 100) + 8 * ((357667643 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12838) *
          (32 * (((4460532913 / 1000000000000000000) : ℝ) + (1488109319 / 1000000000000000000) + (357667643 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12838 : ℝ) ^ 16 *
      (d.w0 12838 164 + d.w1 12838 164 * √(π / 2) + 2 * d.w2 12838 164 +
        energyR16 12838 * radiusPolynomialRoot16 (d.w0 12838 164) (d.w1 12838 164)
          (d.w2 12838 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12838 : ℝ) ^ 16 *
        (((1774712299 / 100000000000000000000) : ℝ) + ((315668479 / 25000000000000000000)) * (126 / 100) + 2 * ((230674533 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12838) *
          (32 * (((1774712299 / 100000000000000000000) : ℝ) + (315668479 / 25000000000000000000) + (230674533 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12838

/-! A coarse bound on the actual paper statistics constant at dimension 12839. -/
namespace BstLean.Part266.Row12839
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12837 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12837 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12837 128 ≤ (13091 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13091 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12839) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12839 : ℕ))
    (by norm_num : (12839 : ℕ) ≤ 16384)
  have ht : paperTail256 12839 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12839 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12839 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12839 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12839 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12839 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12837 128 * √(2 / (12839 : ℝ)) *
      (√(12839 : ℝ) + paperT0 12839 + paperTail256 12839) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12839 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12839 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12839 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12837 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12837 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12839 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12839

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12839
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12839 (61 / 100) 164 (17 / (100 * 12839)) (26 / (10 * 12839)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12839 (61 / 100) 164 (17 / (100 * 12839)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (115309181 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (718493233 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1172219333 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12839 / 12839 * (61 / 100)) ^ 4 * inverseRadius8 (12839 - 1) /
            envelopeGap 12839 (61 / 100) 164 (17 / (100 * 12839)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12839

namespace BstLean.Part266.Row12839
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12839 164 ≤ (4459665357 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12839 164 ≤ (185977473 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (14303921 / 40000000000000000)
  w0 : (tableEnvelope C).w0 12839 164 ≤ (443574457 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12839 164 ≤ (63118949 / 5000000000000000000)
  w2 : (tableEnvelope C).w2 12839 164 ≤ (461241267 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (115309181 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (115309181 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (718493233 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1172219333 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((727761 / 200000000) : ℝ) ≤ √(17 / (100 * 12839) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12839) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (536910563 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3790760433 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12839) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12839) ≤ (55074911 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12839) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12839 * (164 : ℝ) ^ 2 + 26 / (10 * 12839) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12839) : ℝ)) (tA 12839 * 164 ^ 2 + 26 / (10 * 12839)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((727761 / 200000000))) * ((115309181 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((727761 / 200000000)) ^ 3) * ((718493233 / 500000000000000000000000))) + ((1172219333 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((727761 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12839) : ℝ)) d.D d.V d.P (√(tA 12839) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((727761 / 200000000)) ^ 2 * (((536910563 / 250000000000000)) * ((3790760433 / 100000000000000000)))) + ((1172219333 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12839) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((727761 / 200000000)) * ((115309181 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12839) : ℝ)) (tA 12839 * 164 ^ 2 + 26 / (10 * 12839)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((115309181 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((727761 / 200000000)) ^ 2) * ((718493233 / 500000000000000000000000)) + ((1172219333 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12839) : ℝ)) (√(26 / (10 * 12839) : ℝ)) d.D d.V d.P (√(tA 12839) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((727761 / 200000000)) * (((536910563 / 250000000000000)) * ((3790760433 / 100000000000000000))) + ((1172219333 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12839) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((115309181 / 25000000000000000000) : ℝ) + ((1172219333 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12839

namespace BstLean.Part266.Row12839
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12839 164 ∧
    0 ≤ (tableEnvelope C).f1 12839 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12839 164 ∧
    0 ≤ (tableEnvelope C).w1 12839 164 ∧ 0 ≤ (tableEnvelope C).w2 12839 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12839 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12839 164 ∧ 0 ≤ d.f1 12839 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12839 164 ∧ 0 ≤ d.w1 12839 164 ∧ 0 ≤ d.w2 12839 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12839 ≤ 2 * (228 / 100 : ℝ) / 12839 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12839 ≤ 2 * (370 / 100 : ℝ) / 12839 := by
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
    (completeRAData (tableEnvelope C) 12839 164).locationBound 12839 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12839 164).energyBound 12839 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12839 164) (d.f1 12839 164) d.f2 ≤
      32 * (((4459665357 / 1000000000000000000) : ℝ) + (185977473 / 125000000000000000) + (14303921 / 40000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12839 164) (d.w1 12839 164)
      (d.w2 12839 164) ≤
      32 * (((443574457 / 25000000000000000000) : ℝ) + (63118949 / 5000000000000000000) + (461241267 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12839 164) (d.f1 12839 164) d.f2 ≤
      ((4459665357 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4459665357 / 1000000000000000000)) * ((185977473 / 125000000000000000)) * (126 / 100) +
      2 * (((185977473 / 125000000000000000)) ^ 2 + 2 * ((4459665357 / 1000000000000000000)) * ((14303921 / 40000000000000000))) +
      6 * ((185977473 / 125000000000000000)) * ((14303921 / 40000000000000000)) * (126 / 100) + 8 * ((14303921 / 40000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12839 164) (d.f1 12839 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12839 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12839 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12839 164) (d.f1 12839 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12839 164) (d.w1 12839 164) (d.w2 12839 164)
  have hwexpr0 : 0 ≤ d.w0 12839 164 + d.w1 12839 164 * √(π / 2) +
      2 * d.w2 12839 164 + energyR16 12839 *
      radiusPolynomialRoot16 (d.w0 12839 164) (d.w1 12839 164) (d.w2 12839 164) := by
    positivity
  constructor
  · change (12839 : ℝ) ^ 8 * (mA 12839 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12839 164) (d.f1 12839 164) d.f2 + locationR16 12839 *
        radiusPolynomialRoot16 (d.f0 12839 164) (d.f1 12839 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12839 : ℝ) ^ 8 * (mA 12839 : ℝ) ^ 8 *
        ((((4459665357 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4459665357 / 1000000000000000000)) * ((185977473 / 125000000000000000)) * (126 / 100) +
          2 * (((185977473 / 125000000000000000)) ^ 2 + 2 * ((4459665357 / 1000000000000000000)) * ((14303921 / 40000000000000000))) +
          6 * ((185977473 / 125000000000000000)) * ((14303921 / 40000000000000000)) * (126 / 100) + 8 * ((14303921 / 40000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12839) *
          (32 * (((4459665357 / 1000000000000000000) : ℝ) + (185977473 / 125000000000000000) + (14303921 / 40000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12839 : ℝ) ^ 16 *
      (d.w0 12839 164 + d.w1 12839 164 * √(π / 2) + 2 * d.w2 12839 164 +
        energyR16 12839 * radiusPolynomialRoot16 (d.w0 12839 164) (d.w1 12839 164)
          (d.w2 12839 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12839 : ℝ) ^ 16 *
        (((443574457 / 25000000000000000000) : ℝ) + ((63118949 / 5000000000000000000)) * (126 / 100) + 2 * ((461241267 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12839) *
          (32 * (((443574457 / 25000000000000000000) : ℝ) + (63118949 / 5000000000000000000) + (461241267 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12839

/-! A coarse bound on the actual paper statistics constant at dimension 12840. -/
namespace BstLean.Part266.Row12840
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12838 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12838 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12838 128 ≤ (13092 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13092 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12840) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12840 : ℕ))
    (by norm_num : (12840 : ℕ) ≤ 16384)
  have ht : paperTail256 12840 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12840 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12840 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12840 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12840 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12840 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12838 128 * √(2 / (12840 : ℝ)) *
      (√(12840 : ℝ) + paperT0 12840 + paperTail256 12840) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12840 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12840 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12840 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12838 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12838 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12840 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12840

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12840
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12840 (61 / 100) 164 (17 / (100 * 12840)) (26 / (10 * 12840)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12840 (61 / 100) 164 (17 / (100 * 12840)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (230564481 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1436538841 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4685928543 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12840 / 12840 * (61 / 100)) ^ 4 * inverseRadius8 (12840 - 1) /
            envelopeGap 12840 (61 / 100) 164 (17 / (100 * 12840)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12840

namespace BstLean.Part266.Row12840
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12840 164 ≤ (278674881 / 62500000000000000)
  f1 : (tableEnvelope C).f1 12840 164 ≤ (185941293 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (357528429 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12840 164 ≤ (1773883499 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12840 164 ≤ (78880259 / 6250000000000000000)
  w2 : (tableEnvelope C).w2 12840 164 ≤ (230566751 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (230564481 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (230564481 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1436538841 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4685928543 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3638663 / 1000000000) : ℝ) ≤ √(17 / (100 * 12840) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12840) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2147391353 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (296107029 / 7812500000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12840) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12840) ≤ (27535311 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12840) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12840 * (164 : ℝ) ^ 2 + 26 / (10 * 12840) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12840) : ℝ)) (tA 12840 * 164 ^ 2 + 26 / (10 * 12840)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3638663 / 1000000000))) * ((230564481 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3638663 / 1000000000)) ^ 3) * ((1436538841 / 1000000000000000000000000))) + ((4685928543 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3638663 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12840) : ℝ)) d.D d.V d.P (√(tA 12840) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3638663 / 1000000000)) ^ 2 * (((2147391353 / 1000000000000000)) * ((296107029 / 7812500000000000)))) + ((4685928543 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12840) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3638663 / 1000000000)) * ((230564481 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12840) : ℝ)) (tA 12840 * 164 ^ 2 + 26 / (10 * 12840)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((230564481 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3638663 / 1000000000)) ^ 2) * ((1436538841 / 1000000000000000000000000)) + ((4685928543 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12840) : ℝ)) (√(26 / (10 * 12840) : ℝ)) d.D d.V d.P (√(tA 12840) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3638663 / 1000000000)) * (((2147391353 / 1000000000000000)) * ((296107029 / 7812500000000000))) + ((4685928543 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12840) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((230564481 / 50000000000000000000) : ℝ) + ((4685928543 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12840

namespace BstLean.Part266.Row12840
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12840 164 ∧
    0 ≤ (tableEnvelope C).f1 12840 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12840 164 ∧
    0 ≤ (tableEnvelope C).w1 12840 164 ∧ 0 ≤ (tableEnvelope C).w2 12840 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12840 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12840 164 ∧ 0 ≤ d.f1 12840 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12840 164 ∧ 0 ≤ d.w1 12840 164 ∧ 0 ≤ d.w2 12840 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12840 ≤ 2 * (228 / 100 : ℝ) / 12840 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12840 ≤ 2 * (370 / 100 : ℝ) / 12840 := by
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
    (completeRAData (tableEnvelope C) 12840 164).locationBound 12840 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12840 164).energyBound 12840 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12840 164) (d.f1 12840 164) d.f2 ≤
      32 * (((278674881 / 62500000000000000) : ℝ) + (185941293 / 125000000000000000) + (357528429 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12840 164) (d.w1 12840 164)
      (d.w2 12840 164) ≤
      32 * (((1773883499 / 100000000000000000000) : ℝ) + (78880259 / 6250000000000000000) + (230566751 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12840 164) (d.f1 12840 164) d.f2 ≤
      ((278674881 / 62500000000000000) : ℝ) ^ 2 + 2 * ((278674881 / 62500000000000000)) * ((185941293 / 125000000000000000)) * (126 / 100) +
      2 * (((185941293 / 125000000000000000)) ^ 2 + 2 * ((278674881 / 62500000000000000)) * ((357528429 / 1000000000000000000))) +
      6 * ((185941293 / 125000000000000000)) * ((357528429 / 1000000000000000000)) * (126 / 100) + 8 * ((357528429 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12840 164) (d.f1 12840 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12840 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12840 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12840 164) (d.f1 12840 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12840 164) (d.w1 12840 164) (d.w2 12840 164)
  have hwexpr0 : 0 ≤ d.w0 12840 164 + d.w1 12840 164 * √(π / 2) +
      2 * d.w2 12840 164 + energyR16 12840 *
      radiusPolynomialRoot16 (d.w0 12840 164) (d.w1 12840 164) (d.w2 12840 164) := by
    positivity
  constructor
  · change (12840 : ℝ) ^ 8 * (mA 12840 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12840 164) (d.f1 12840 164) d.f2 + locationR16 12840 *
        radiusPolynomialRoot16 (d.f0 12840 164) (d.f1 12840 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12840 : ℝ) ^ 8 * (mA 12840 : ℝ) ^ 8 *
        ((((278674881 / 62500000000000000) : ℝ) ^ 2 + 2 * ((278674881 / 62500000000000000)) * ((185941293 / 125000000000000000)) * (126 / 100) +
          2 * (((185941293 / 125000000000000000)) ^ 2 + 2 * ((278674881 / 62500000000000000)) * ((357528429 / 1000000000000000000))) +
          6 * ((185941293 / 125000000000000000)) * ((357528429 / 1000000000000000000)) * (126 / 100) + 8 * ((357528429 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12840) *
          (32 * (((278674881 / 62500000000000000) : ℝ) + (185941293 / 125000000000000000) + (357528429 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12840 : ℝ) ^ 16 *
      (d.w0 12840 164 + d.w1 12840 164 * √(π / 2) + 2 * d.w2 12840 164 +
        energyR16 12840 * radiusPolynomialRoot16 (d.w0 12840 164) (d.w1 12840 164)
          (d.w2 12840 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12840 : ℝ) ^ 16 *
        (((1773883499 / 100000000000000000000) : ℝ) + ((78880259 / 6250000000000000000)) * (126 / 100) + 2 * ((230566751 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12840) *
          (32 * (((1773883499 / 100000000000000000000) : ℝ) + (78880259 / 6250000000000000000) + (230566751 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12840

/-! A coarse bound on the actual paper statistics constant at dimension 12841. -/
namespace BstLean.Part266.Row12841
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12839 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12839 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12839 128 ≤ (13093 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13093 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12841) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12841 : ℕ))
    (by norm_num : (12841 : ℕ) ≤ 16384)
  have ht : paperTail256 12841 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12841 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12841 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12841 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12841 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12841 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12839 128 * √(2 / (12841 : ℝ)) *
      (√(12841 : ℝ) + paperT0 12841 + paperTail256 12841) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12841 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12841 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12841 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12839 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12839 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12841 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12841

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12841
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12841 (61 / 100) 164 (17 / (100 * 12841)) (26 / (10 * 12841)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12841 (61 / 100) 164 (17 / (100 * 12841)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (28813827 / 6250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1436091391 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4682981843 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12841 / 12841 * (61 / 100)) ^ 4 * inverseRadius8 (12841 - 1) /
            envelopeGap 12841 (61 / 100) 164 (17 / (100 * 12841)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12841

namespace BstLean.Part266.Row12841
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12841 164 ≤ (2228963797 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12841 164 ≤ (1487240177 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (178729377 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12841 164 ≤ (443367147 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12841 164 ≤ (9857727 / 781250000000000000)
  w2 : (tableEnvelope C).w2 12841 164 ≤ (461025769 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (28813827 / 6250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (28813827 / 6250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1436091391 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4682981843 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1819261 / 500000000) : ℝ) ≤ √(17 / (100 * 12841) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12841) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2147140499 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18947898241 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12841) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12841) ≤ (55066333 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12841) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12841 * (164 : ℝ) ^ 2 + 26 / (10 * 12841) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12841) : ℝ)) (tA 12841 * 164 ^ 2 + 26 / (10 * 12841)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1819261 / 500000000))) * ((28813827 / 6250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1819261 / 500000000)) ^ 3) * ((1436091391 / 1000000000000000000000000))) + ((4682981843 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1819261 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12841) : ℝ)) d.D d.V d.P (√(tA 12841) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1819261 / 500000000)) ^ 2 * (((2147140499 / 1000000000000000)) * ((18947898241 / 500000000000000000)))) + ((4682981843 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12841) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1819261 / 500000000)) * ((28813827 / 6250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12841) : ℝ)) (tA 12841 * 164 ^ 2 + 26 / (10 * 12841)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((28813827 / 6250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1819261 / 500000000)) ^ 2) * ((1436091391 / 1000000000000000000000000)) + ((4682981843 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12841) : ℝ)) (√(26 / (10 * 12841) : ℝ)) d.D d.V d.P (√(tA 12841) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1819261 / 500000000)) * (((2147140499 / 1000000000000000)) * ((18947898241 / 500000000000000000))) + ((4682981843 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12841) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((28813827 / 6250000000000000000) : ℝ) + ((4682981843 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12841

namespace BstLean.Part266.Row12841
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12841 164 ∧
    0 ≤ (tableEnvelope C).f1 12841 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12841 164 ∧
    0 ≤ (tableEnvelope C).w1 12841 164 ∧ 0 ≤ (tableEnvelope C).w2 12841 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12841 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12841 164 ∧ 0 ≤ d.f1 12841 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12841 164 ∧ 0 ≤ d.w1 12841 164 ∧ 0 ≤ d.w2 12841 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12841 ≤ 2 * (228 / 100 : ℝ) / 12841 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12841 ≤ 2 * (370 / 100 : ℝ) / 12841 := by
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
    (completeRAData (tableEnvelope C) 12841 164).locationBound 12841 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12841 164).energyBound 12841 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12841 164) (d.f1 12841 164) d.f2 ≤
      32 * (((2228963797 / 500000000000000000) : ℝ) + (1487240177 / 1000000000000000000) + (178729377 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12841 164) (d.w1 12841 164)
      (d.w2 12841 164) ≤
      32 * (((443367147 / 25000000000000000000) : ℝ) + (9857727 / 781250000000000000) + (461025769 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12841 164) (d.f1 12841 164) d.f2 ≤
      ((2228963797 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2228963797 / 500000000000000000)) * ((1487240177 / 1000000000000000000)) * (126 / 100) +
      2 * (((1487240177 / 1000000000000000000)) ^ 2 + 2 * ((2228963797 / 500000000000000000)) * ((178729377 / 500000000000000000))) +
      6 * ((1487240177 / 1000000000000000000)) * ((178729377 / 500000000000000000)) * (126 / 100) + 8 * ((178729377 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12841 164) (d.f1 12841 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12841 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12841 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12841 164) (d.f1 12841 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12841 164) (d.w1 12841 164) (d.w2 12841 164)
  have hwexpr0 : 0 ≤ d.w0 12841 164 + d.w1 12841 164 * √(π / 2) +
      2 * d.w2 12841 164 + energyR16 12841 *
      radiusPolynomialRoot16 (d.w0 12841 164) (d.w1 12841 164) (d.w2 12841 164) := by
    positivity
  constructor
  · change (12841 : ℝ) ^ 8 * (mA 12841 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12841 164) (d.f1 12841 164) d.f2 + locationR16 12841 *
        radiusPolynomialRoot16 (d.f0 12841 164) (d.f1 12841 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12841 : ℝ) ^ 8 * (mA 12841 : ℝ) ^ 8 *
        ((((2228963797 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2228963797 / 500000000000000000)) * ((1487240177 / 1000000000000000000)) * (126 / 100) +
          2 * (((1487240177 / 1000000000000000000)) ^ 2 + 2 * ((2228963797 / 500000000000000000)) * ((178729377 / 500000000000000000))) +
          6 * ((1487240177 / 1000000000000000000)) * ((178729377 / 500000000000000000)) * (126 / 100) + 8 * ((178729377 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12841) *
          (32 * (((2228963797 / 500000000000000000) : ℝ) + (1487240177 / 1000000000000000000) + (178729377 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12841 : ℝ) ^ 16 *
      (d.w0 12841 164 + d.w1 12841 164 * √(π / 2) + 2 * d.w2 12841 164 +
        energyR16 12841 * radiusPolynomialRoot16 (d.w0 12841 164) (d.w1 12841 164)
          (d.w2 12841 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12841 : ℝ) ^ 16 *
        (((443367147 / 25000000000000000000) : ℝ) + ((9857727 / 781250000000000000)) * (126 / 100) + 2 * ((461025769 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12841) *
          (32 * (((443367147 / 25000000000000000000) : ℝ) + (9857727 / 781250000000000000) + (461025769 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12841

/-! A coarse bound on the actual paper statistics constant at dimension 12842. -/
namespace BstLean.Part266.Row12842
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12840 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12840 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12840 128 ≤ (13094 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13094 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12842) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12842 : ℕ))
    (by norm_num : (12842 : ℕ) ≤ 16384)
  have ht : paperTail256 12842 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12842 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12842 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12842 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12842 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12842 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12840 128 * √(2 / (12842 : ℝ)) *
      (√(12842 : ℝ) + paperT0 12842 + paperTail256 12842) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12842 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12842 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12842 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12840 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12840 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12842 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12842

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12842
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12842 (61 / 100) 164 (17 / (100 * 12842)) (26 / (10 * 12842)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12842 (61 / 100) 164 (17 / (100 * 12842)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (460913537 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (287128823 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4680037229 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12842 / 12842 * (61 / 100)) ^ 4 * inverseRadius8 (12842 - 1) /
            envelopeGap 12842 (61 / 100) 164 (17 / (100 * 12842)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12842

namespace BstLean.Part266.Row12842
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12842 164 ≤ (178282437 / 40000000000000000)
  f1 : (tableEnvelope C).f1 12842 164 ≤ (1486950921 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (357389199 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12842 164 ≤ (886527271 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12842 164 ≤ (252298883 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12842 164 ≤ (460918071 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (460913537 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (460913537 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (287128823 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4680037229 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((181919 / 50000000) : ℝ) ≤ √(17 / (100 * 12842) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12842) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2146889697 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3788989463 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12842) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12842) ≤ (11012409 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12842) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12842 * (164 : ℝ) ^ 2 + 26 / (10 * 12842) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12842) : ℝ)) (tA 12842 * 164 ^ 2 + 26 / (10 * 12842)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((181919 / 50000000))) * ((460913537 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((181919 / 50000000)) ^ 3) * ((287128823 / 200000000000000000000000))) + ((4680037229 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((181919 / 50000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12842) : ℝ)) d.D d.V d.P (√(tA 12842) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((181919 / 50000000)) ^ 2 * (((2146889697 / 1000000000000000)) * ((3788989463 / 100000000000000000)))) + ((4680037229 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12842) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((181919 / 50000000)) * ((460913537 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12842) : ℝ)) (tA 12842 * 164 ^ 2 + 26 / (10 * 12842)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((460913537 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((181919 / 50000000)) ^ 2) * ((287128823 / 200000000000000000000000)) + ((4680037229 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12842) : ℝ)) (√(26 / (10 * 12842) : ℝ)) d.D d.V d.P (√(tA 12842) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((181919 / 50000000)) * (((2146889697 / 1000000000000000)) * ((3788989463 / 100000000000000000))) + ((4680037229 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12842) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((460913537 / 100000000000000000000) : ℝ) + ((4680037229 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12842

namespace BstLean.Part266.Row12842
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12842 164 ∧
    0 ≤ (tableEnvelope C).f1 12842 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12842 164 ∧
    0 ≤ (tableEnvelope C).w1 12842 164 ∧ 0 ≤ (tableEnvelope C).w2 12842 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12842 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12842 164 ∧ 0 ≤ d.f1 12842 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12842 164 ∧ 0 ≤ d.w1 12842 164 ∧ 0 ≤ d.w2 12842 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12842 ≤ 2 * (228 / 100 : ℝ) / 12842 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12842 ≤ 2 * (370 / 100 : ℝ) / 12842 := by
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
    (completeRAData (tableEnvelope C) 12842 164).locationBound 12842 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12842 164).energyBound 12842 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12842 164) (d.f1 12842 164) d.f2 ≤
      32 * (((178282437 / 40000000000000000) : ℝ) + (1486950921 / 1000000000000000000) + (357389199 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12842 164) (d.w1 12842 164)
      (d.w2 12842 164) ≤
      32 * (((886527271 / 50000000000000000000) : ℝ) + (252298883 / 20000000000000000000) + (460918071 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12842 164) (d.f1 12842 164) d.f2 ≤
      ((178282437 / 40000000000000000) : ℝ) ^ 2 + 2 * ((178282437 / 40000000000000000)) * ((1486950921 / 1000000000000000000)) * (126 / 100) +
      2 * (((1486950921 / 1000000000000000000)) ^ 2 + 2 * ((178282437 / 40000000000000000)) * ((357389199 / 1000000000000000000))) +
      6 * ((1486950921 / 1000000000000000000)) * ((357389199 / 1000000000000000000)) * (126 / 100) + 8 * ((357389199 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12842 164) (d.f1 12842 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12842 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12842 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12842 164) (d.f1 12842 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12842 164) (d.w1 12842 164) (d.w2 12842 164)
  have hwexpr0 : 0 ≤ d.w0 12842 164 + d.w1 12842 164 * √(π / 2) +
      2 * d.w2 12842 164 + energyR16 12842 *
      radiusPolynomialRoot16 (d.w0 12842 164) (d.w1 12842 164) (d.w2 12842 164) := by
    positivity
  constructor
  · change (12842 : ℝ) ^ 8 * (mA 12842 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12842 164) (d.f1 12842 164) d.f2 + locationR16 12842 *
        radiusPolynomialRoot16 (d.f0 12842 164) (d.f1 12842 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12842 : ℝ) ^ 8 * (mA 12842 : ℝ) ^ 8 *
        ((((178282437 / 40000000000000000) : ℝ) ^ 2 + 2 * ((178282437 / 40000000000000000)) * ((1486950921 / 1000000000000000000)) * (126 / 100) +
          2 * (((1486950921 / 1000000000000000000)) ^ 2 + 2 * ((178282437 / 40000000000000000)) * ((357389199 / 1000000000000000000))) +
          6 * ((1486950921 / 1000000000000000000)) * ((357389199 / 1000000000000000000)) * (126 / 100) + 8 * ((357389199 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12842) *
          (32 * (((178282437 / 40000000000000000) : ℝ) + (1486950921 / 1000000000000000000) + (357389199 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12842 : ℝ) ^ 16 *
      (d.w0 12842 164 + d.w1 12842 164 * √(π / 2) + 2 * d.w2 12842 164 +
        energyR16 12842 * radiusPolynomialRoot16 (d.w0 12842 164) (d.w1 12842 164)
          (d.w2 12842 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12842 : ℝ) ^ 16 *
        (((886527271 / 50000000000000000000) : ℝ) + ((252298883 / 20000000000000000000)) * (126 / 100) + 2 * ((460918071 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12842) *
          (32 * (((886527271 / 50000000000000000000) : ℝ) + (252298883 / 20000000000000000000) + (460918071 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12842

/-! A coarse bound on the actual paper statistics constant at dimension 12843. -/
namespace BstLean.Part266.Row12843
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12841 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12841 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12841 128 ≤ (13095 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13095 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12843) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12843 : ℕ))
    (by norm_num : (12843 : ℕ) ≤ 16384)
  have ht : paperTail256 12843 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12843 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12843 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12843 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12843 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12843 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12841 128 * √(2 / (12843 : ℝ)) *
      (√(12843 : ℝ) + paperT0 12843 + paperTail256 12843) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12843 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12843 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12843 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12841 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12841 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12843 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12843

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12843
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12843 (61 / 100) 164 (17 / (100 * 12843)) (26 / (10 * 12843)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12843 (61 / 100) 164 (17 / (100 * 12843)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (3686447 / 800000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1435197013 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (46770947 / 10000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12843 / 12843 * (61 / 100)) ^ 4 * inverseRadius8 (12843 - 1) /
            envelopeGap 12843 (61 / 100) 164 (17 / (100 * 12843)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12843

namespace BstLean.Part266.Row12843
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12843 164 ≤ (4456194549 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12843 164 ≤ (1486661757 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (71463933 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12843 164 ≤ (354528127 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12843 164 ≤ (1261199871 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12843 164 ≤ (230405203 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (3686447 / 800000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (3686447 / 800000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1435197013 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (46770947 / 10000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1819119 / 500000000) : ℝ) ≤ √(17 / (100 * 12843) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12843) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2146638943 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18941997077 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12843) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12843) ≤ (27528879 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12843) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12843 * (164 : ℝ) ^ 2 + 26 / (10 * 12843) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12843) : ℝ)) (tA 12843 * 164 ^ 2 + 26 / (10 * 12843)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1819119 / 500000000))) * ((3686447 / 800000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1819119 / 500000000)) ^ 3) * ((1435197013 / 1000000000000000000000000))) + ((46770947 / 10000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1819119 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12843) : ℝ)) d.D d.V d.P (√(tA 12843) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1819119 / 500000000)) ^ 2 * (((2146638943 / 1000000000000000)) * ((18941997077 / 500000000000000000)))) + ((46770947 / 10000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12843) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1819119 / 500000000)) * ((3686447 / 800000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12843) : ℝ)) (tA 12843 * 164 ^ 2 + 26 / (10 * 12843)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((3686447 / 800000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1819119 / 500000000)) ^ 2) * ((1435197013 / 1000000000000000000000000)) + ((46770947 / 10000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12843) : ℝ)) (√(26 / (10 * 12843) : ℝ)) d.D d.V d.P (√(tA 12843) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1819119 / 500000000)) * (((2146638943 / 1000000000000000)) * ((18941997077 / 500000000000000000))) + ((46770947 / 10000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12843) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((3686447 / 800000000000000000) : ℝ) + ((46770947 / 10000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12843

namespace BstLean.Part266.Row12843
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12843 164 ∧
    0 ≤ (tableEnvelope C).f1 12843 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12843 164 ∧
    0 ≤ (tableEnvelope C).w1 12843 164 ∧ 0 ≤ (tableEnvelope C).w2 12843 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12843 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12843 164 ∧ 0 ≤ d.f1 12843 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12843 164 ∧ 0 ≤ d.w1 12843 164 ∧ 0 ≤ d.w2 12843 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12843 ≤ 2 * (228 / 100 : ℝ) / 12843 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12843 ≤ 2 * (370 / 100 : ℝ) / 12843 := by
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
    (completeRAData (tableEnvelope C) 12843 164).locationBound 12843 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12843 164).energyBound 12843 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12843 164) (d.f1 12843 164) d.f2 ≤
      32 * (((4456194549 / 1000000000000000000) : ℝ) + (1486661757 / 1000000000000000000) + (71463933 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12843 164) (d.w1 12843 164)
      (d.w2 12843 164) ≤
      32 * (((354528127 / 20000000000000000000) : ℝ) + (1261199871 / 100000000000000000000) + (230405203 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12843 164) (d.f1 12843 164) d.f2 ≤
      ((4456194549 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4456194549 / 1000000000000000000)) * ((1486661757 / 1000000000000000000)) * (126 / 100) +
      2 * (((1486661757 / 1000000000000000000)) ^ 2 + 2 * ((4456194549 / 1000000000000000000)) * ((71463933 / 200000000000000000))) +
      6 * ((1486661757 / 1000000000000000000)) * ((71463933 / 200000000000000000)) * (126 / 100) + 8 * ((71463933 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12843 164) (d.f1 12843 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12843 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12843 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12843 164) (d.f1 12843 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12843 164) (d.w1 12843 164) (d.w2 12843 164)
  have hwexpr0 : 0 ≤ d.w0 12843 164 + d.w1 12843 164 * √(π / 2) +
      2 * d.w2 12843 164 + energyR16 12843 *
      radiusPolynomialRoot16 (d.w0 12843 164) (d.w1 12843 164) (d.w2 12843 164) := by
    positivity
  constructor
  · change (12843 : ℝ) ^ 8 * (mA 12843 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12843 164) (d.f1 12843 164) d.f2 + locationR16 12843 *
        radiusPolynomialRoot16 (d.f0 12843 164) (d.f1 12843 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12843 : ℝ) ^ 8 * (mA 12843 : ℝ) ^ 8 *
        ((((4456194549 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4456194549 / 1000000000000000000)) * ((1486661757 / 1000000000000000000)) * (126 / 100) +
          2 * (((1486661757 / 1000000000000000000)) ^ 2 + 2 * ((4456194549 / 1000000000000000000)) * ((71463933 / 200000000000000000))) +
          6 * ((1486661757 / 1000000000000000000)) * ((71463933 / 200000000000000000)) * (126 / 100) + 8 * ((71463933 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12843) *
          (32 * (((4456194549 / 1000000000000000000) : ℝ) + (1486661757 / 1000000000000000000) + (71463933 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12843 : ℝ) ^ 16 *
      (d.w0 12843 164 + d.w1 12843 164 * √(π / 2) + 2 * d.w2 12843 164 +
        energyR16 12843 * radiusPolynomialRoot16 (d.w0 12843 164) (d.w1 12843 164)
          (d.w2 12843 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12843 : ℝ) ^ 16 *
        (((354528127 / 20000000000000000000) : ℝ) + ((1261199871 / 100000000000000000000)) * (126 / 100) + 2 * ((230405203 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12843) *
          (32 * (((354528127 / 20000000000000000000) : ℝ) + (1261199871 / 100000000000000000000) + (230405203 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12843

/-! A coarse bound on the actual paper statistics constant at dimension 12844. -/
namespace BstLean.Part266.Row12844
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12842 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12842 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12842 128 ≤ (13096 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13096 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12844) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12844 : ℕ))
    (by norm_num : (12844 : ℕ) ≤ 16384)
  have ht : paperTail256 12844 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12844 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12844 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12844 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12844 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12844 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12842 128 * √(2 / (12844 : ℝ)) *
      (√(12844 : ℝ) + paperT0 12844 + paperTail256 12844) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12844 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12844 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12844 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12842 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12842 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12844 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12844

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12844
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12844 (61 / 100) 164 (17 / (100 * 12844)) (26 / (10 * 12844)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12844 (61 / 100) 164 (17 / (100 * 12844)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (230349123 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (717375043 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2337077127 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12844 / 12844 * (61 / 100)) ^ 4 * inverseRadius8 (12844 - 1) /
            envelopeGap 12844 (61 / 100) 164 (17 / (100 * 12844)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12844

namespace BstLean.Part266.Row12844
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12844 164 ≤ (556915617 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12844 164 ≤ (1486371869 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (89312513 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12844 164 ≤ (1772226149 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12844 164 ≤ (1260905077 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12844 164 ≤ (230351387 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (230349123 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (230349123 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (717375043 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2337077127 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3638097 / 1000000000) : ℝ) ≤ √(17 / (100 * 12844) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12844) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2146388237 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37878095069 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12844) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12844) ≤ (55053471 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12844) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12844 * (164 : ℝ) ^ 2 + 26 / (10 * 12844) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12844) : ℝ)) (tA 12844 * 164 ^ 2 + 26 / (10 * 12844)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3638097 / 1000000000))) * ((230349123 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3638097 / 1000000000)) ^ 3) * ((717375043 / 500000000000000000000000))) + ((2337077127 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3638097 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12844) : ℝ)) d.D d.V d.P (√(tA 12844) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3638097 / 1000000000)) ^ 2 * (((2146388237 / 1000000000000000)) * ((37878095069 / 1000000000000000000)))) + ((2337077127 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12844) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3638097 / 1000000000)) * ((230349123 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12844) : ℝ)) (tA 12844 * 164 ^ 2 + 26 / (10 * 12844)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((230349123 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3638097 / 1000000000)) ^ 2) * ((717375043 / 500000000000000000000000)) + ((2337077127 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12844) : ℝ)) (√(26 / (10 * 12844) : ℝ)) d.D d.V d.P (√(tA 12844) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3638097 / 1000000000)) * (((2146388237 / 1000000000000000)) * ((37878095069 / 1000000000000000000))) + ((2337077127 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12844) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((230349123 / 50000000000000000000) : ℝ) + ((2337077127 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12844

namespace BstLean.Part266.Row12844
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12844 164 ∧
    0 ≤ (tableEnvelope C).f1 12844 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12844 164 ∧
    0 ≤ (tableEnvelope C).w1 12844 164 ∧ 0 ≤ (tableEnvelope C).w2 12844 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12844 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12844 164 ∧ 0 ≤ d.f1 12844 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12844 164 ∧ 0 ≤ d.w1 12844 164 ∧ 0 ≤ d.w2 12844 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12844 ≤ 2 * (228 / 100 : ℝ) / 12844 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12844 ≤ 2 * (370 / 100 : ℝ) / 12844 := by
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
    (completeRAData (tableEnvelope C) 12844 164).locationBound 12844 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12844 164).energyBound 12844 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12844 164) (d.f1 12844 164) d.f2 ≤
      32 * (((556915617 / 125000000000000000) : ℝ) + (1486371869 / 1000000000000000000) + (89312513 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12844 164) (d.w1 12844 164)
      (d.w2 12844 164) ≤
      32 * (((1772226149 / 100000000000000000000) : ℝ) + (1260905077 / 100000000000000000000) + (230351387 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12844 164) (d.f1 12844 164) d.f2 ≤
      ((556915617 / 125000000000000000) : ℝ) ^ 2 + 2 * ((556915617 / 125000000000000000)) * ((1486371869 / 1000000000000000000)) * (126 / 100) +
      2 * (((1486371869 / 1000000000000000000)) ^ 2 + 2 * ((556915617 / 125000000000000000)) * ((89312513 / 250000000000000000))) +
      6 * ((1486371869 / 1000000000000000000)) * ((89312513 / 250000000000000000)) * (126 / 100) + 8 * ((89312513 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12844 164) (d.f1 12844 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12844 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12844 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12844 164) (d.f1 12844 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12844 164) (d.w1 12844 164) (d.w2 12844 164)
  have hwexpr0 : 0 ≤ d.w0 12844 164 + d.w1 12844 164 * √(π / 2) +
      2 * d.w2 12844 164 + energyR16 12844 *
      radiusPolynomialRoot16 (d.w0 12844 164) (d.w1 12844 164) (d.w2 12844 164) := by
    positivity
  constructor
  · change (12844 : ℝ) ^ 8 * (mA 12844 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12844 164) (d.f1 12844 164) d.f2 + locationR16 12844 *
        radiusPolynomialRoot16 (d.f0 12844 164) (d.f1 12844 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12844 : ℝ) ^ 8 * (mA 12844 : ℝ) ^ 8 *
        ((((556915617 / 125000000000000000) : ℝ) ^ 2 + 2 * ((556915617 / 125000000000000000)) * ((1486371869 / 1000000000000000000)) * (126 / 100) +
          2 * (((1486371869 / 1000000000000000000)) ^ 2 + 2 * ((556915617 / 125000000000000000)) * ((89312513 / 250000000000000000))) +
          6 * ((1486371869 / 1000000000000000000)) * ((89312513 / 250000000000000000)) * (126 / 100) + 8 * ((89312513 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12844) *
          (32 * (((556915617 / 125000000000000000) : ℝ) + (1486371869 / 1000000000000000000) + (89312513 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12844 : ℝ) ^ 16 *
      (d.w0 12844 164 + d.w1 12844 164 * √(π / 2) + 2 * d.w2 12844 164 +
        energyR16 12844 * radiusPolynomialRoot16 (d.w0 12844 164) (d.w1 12844 164)
          (d.w2 12844 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12844 : ℝ) ^ 16 *
        (((1772226149 / 100000000000000000000) : ℝ) + ((1260905077 / 100000000000000000000)) * (126 / 100) + 2 * ((230351387 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12844) *
          (32 * (((1772226149 / 100000000000000000000) : ℝ) + (1260905077 / 100000000000000000000) + (230351387 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12844

/-! A coarse bound on the actual paper statistics constant at dimension 12845. -/
namespace BstLean.Part266.Row12845
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12843 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12843 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12843 128 ≤ (13097 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13097 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12845) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12845 : ℕ))
    (by norm_num : (12845 : ℕ) ≤ 16384)
  have ht : paperTail256 12845 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12845 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12845 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12845 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12845 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12845 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12843 128 * √(2 / (12845 : ℝ)) *
      (√(12845 : ℝ) + paperT0 12845 + paperTail256 12845) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12845 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12845 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12845 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12843 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12843 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12845 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12845

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12845
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12845 (61 / 100) 164 (17 / (100 * 12845)) (26 / (10 * 12845)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12845 (61 / 100) 164 (17 / (100 * 12845)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (460590651 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (358575833 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (467121589 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12845 / 12845 * (61 / 100)) ^ 4 * inverseRadius8 (12845 - 1) /
            envelopeGap 12845 (61 / 100) 164 (17 / (100 * 12845)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12845

namespace BstLean.Part266.Row12845
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12845 164 ≤ (89089183 / 20000000000000000)
  f1 : (tableEnvelope C).f1 12845 164 ≤ (1486082889 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (178590279 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12845 164 ≤ (442953131 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12845 164 ≤ (1260610727 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12845 164 ≤ (57574397 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (460590651 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (460590651 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (358575833 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (467121589 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((727591 / 200000000) : ℝ) ≤ √(17 / (100 * 12845) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12845) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (107306879 / 50000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37872197349 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12845) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12845) ≤ (11009837 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12845) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12845 * (164 : ℝ) ^ 2 + 26 / (10 * 12845) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12845) : ℝ)) (tA 12845 * 164 ^ 2 + 26 / (10 * 12845)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((727591 / 200000000))) * ((460590651 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((727591 / 200000000)) ^ 3) * ((358575833 / 250000000000000000000000))) + ((467121589 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((727591 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12845) : ℝ)) d.D d.V d.P (√(tA 12845) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((727591 / 200000000)) ^ 2 * (((107306879 / 50000000000000)) * ((37872197349 / 1000000000000000000)))) + ((467121589 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12845) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((727591 / 200000000)) * ((460590651 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12845) : ℝ)) (tA 12845 * 164 ^ 2 + 26 / (10 * 12845)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((460590651 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((727591 / 200000000)) ^ 2) * ((358575833 / 250000000000000000000000)) + ((467121589 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12845) : ℝ)) (√(26 / (10 * 12845) : ℝ)) d.D d.V d.P (√(tA 12845) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((727591 / 200000000)) * (((107306879 / 50000000000000)) * ((37872197349 / 1000000000000000000))) + ((467121589 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12845) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((460590651 / 100000000000000000000) : ℝ) + ((467121589 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12845

namespace BstLean.Part266.Row12845
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12845 164 ∧
    0 ≤ (tableEnvelope C).f1 12845 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12845 164 ∧
    0 ≤ (tableEnvelope C).w1 12845 164 ∧ 0 ≤ (tableEnvelope C).w2 12845 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12845 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12845 164 ∧ 0 ≤ d.f1 12845 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12845 164 ∧ 0 ≤ d.w1 12845 164 ∧ 0 ≤ d.w2 12845 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12845 ≤ 2 * (228 / 100 : ℝ) / 12845 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12845 ≤ 2 * (370 / 100 : ℝ) / 12845 := by
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
    (completeRAData (tableEnvelope C) 12845 164).locationBound 12845 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12845 164).energyBound 12845 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12845 164) (d.f1 12845 164) d.f2 ≤
      32 * (((89089183 / 20000000000000000) : ℝ) + (1486082889 / 1000000000000000000) + (178590279 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12845 164) (d.w1 12845 164)
      (d.w2 12845 164) ≤
      32 * (((442953131 / 25000000000000000000) : ℝ) + (1260610727 / 100000000000000000000) + (57574397 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12845 164) (d.f1 12845 164) d.f2 ≤
      ((89089183 / 20000000000000000) : ℝ) ^ 2 + 2 * ((89089183 / 20000000000000000)) * ((1486082889 / 1000000000000000000)) * (126 / 100) +
      2 * (((1486082889 / 1000000000000000000)) ^ 2 + 2 * ((89089183 / 20000000000000000)) * ((178590279 / 500000000000000000))) +
      6 * ((1486082889 / 1000000000000000000)) * ((178590279 / 500000000000000000)) * (126 / 100) + 8 * ((178590279 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12845 164) (d.f1 12845 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12845 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12845 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12845 164) (d.f1 12845 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12845 164) (d.w1 12845 164) (d.w2 12845 164)
  have hwexpr0 : 0 ≤ d.w0 12845 164 + d.w1 12845 164 * √(π / 2) +
      2 * d.w2 12845 164 + energyR16 12845 *
      radiusPolynomialRoot16 (d.w0 12845 164) (d.w1 12845 164) (d.w2 12845 164) := by
    positivity
  constructor
  · change (12845 : ℝ) ^ 8 * (mA 12845 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12845 164) (d.f1 12845 164) d.f2 + locationR16 12845 *
        radiusPolynomialRoot16 (d.f0 12845 164) (d.f1 12845 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12845 : ℝ) ^ 8 * (mA 12845 : ℝ) ^ 8 *
        ((((89089183 / 20000000000000000) : ℝ) ^ 2 + 2 * ((89089183 / 20000000000000000)) * ((1486082889 / 1000000000000000000)) * (126 / 100) +
          2 * (((1486082889 / 1000000000000000000)) ^ 2 + 2 * ((89089183 / 20000000000000000)) * ((178590279 / 500000000000000000))) +
          6 * ((1486082889 / 1000000000000000000)) * ((178590279 / 500000000000000000)) * (126 / 100) + 8 * ((178590279 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12845) *
          (32 * (((89089183 / 20000000000000000) : ℝ) + (1486082889 / 1000000000000000000) + (178590279 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12845 : ℝ) ^ 16 *
      (d.w0 12845 164 + d.w1 12845 164 * √(π / 2) + 2 * d.w2 12845 164 +
        energyR16 12845 * radiusPolynomialRoot16 (d.w0 12845 164) (d.w1 12845 164)
          (d.w2 12845 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12845 : ℝ) ^ 16 *
        (((442953131 / 25000000000000000000) : ℝ) + ((1260610727 / 100000000000000000000)) * (126 / 100) + 2 * ((57574397 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12845) *
          (32 * (((442953131 / 25000000000000000000) : ℝ) + (1260610727 / 100000000000000000000) + (57574397 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12845

/-! A coarse bound on the actual paper statistics constant at dimension 12846. -/
namespace BstLean.Part266.Row12846
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12844 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12844 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12844 128 ≤ (13098 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13098 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12846) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12846 : ℕ))
    (by norm_num : (12846 : ℕ) ≤ 16384)
  have ht : paperTail256 12846 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12846 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12846 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12846 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12846 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12846 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12844 128 * √(2 / (12846 : ℝ)) *
      (√(12846 : ℝ) + paperT0 12846 + paperTail256 12846) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12846 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12846 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12846 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12844 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12844 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12846 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12846

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12846
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12846 (61 / 100) 164 (17 / (100 * 12846)) (26 / (10 * 12846)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12846 (61 / 100) 164 (17 / (100 * 12846)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (460483089 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (89616047 / 62500000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2334139803 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12846 / 12846 * (61 / 100)) ^ 4 * inverseRadius8 (12846 - 1) /
            envelopeGap 12846 (61 / 100) 164 (17 / (100 * 12846)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12846

namespace BstLean.Part266.Row12846
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12846 164 ≤ (1113397531 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12846 164 ≤ (297158637 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (178555493 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12846 164 ≤ (1771398319 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12846 164 ≤ (39384879 / 3125000000000000000)
  w2 : (tableEnvelope C).w2 12846 164 ≤ (115121903 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (460483089 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (460483089 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (89616047 / 62500000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2334139803 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1818907 / 500000000) : ℝ) ≤ √(17 / (100 * 12846) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12846) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2145886971 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (2366643813 / 62500000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12846) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12846) ≤ (550449 / 5000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12846) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12846 * (164 : ℝ) ^ 2 + 26 / (10 * 12846) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12846) : ℝ)) (tA 12846 * 164 ^ 2 + 26 / (10 * 12846)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1818907 / 500000000))) * ((460483089 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1818907 / 500000000)) ^ 3) * ((89616047 / 62500000000000000000000))) + ((2334139803 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1818907 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12846) : ℝ)) d.D d.V d.P (√(tA 12846) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1818907 / 500000000)) ^ 2 * (((2145886971 / 1000000000000000)) * ((2366643813 / 62500000000000000)))) + ((2334139803 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12846) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1818907 / 500000000)) * ((460483089 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12846) : ℝ)) (tA 12846 * 164 ^ 2 + 26 / (10 * 12846)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((460483089 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1818907 / 500000000)) ^ 2) * ((89616047 / 62500000000000000000000)) + ((2334139803 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12846) : ℝ)) (√(26 / (10 * 12846) : ℝ)) d.D d.V d.P (√(tA 12846) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1818907 / 500000000)) * (((2145886971 / 1000000000000000)) * ((2366643813 / 62500000000000000))) + ((2334139803 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12846) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((460483089 / 100000000000000000000) : ℝ) + ((2334139803 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12846

namespace BstLean.Part266.Row12846
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12846 164 ∧
    0 ≤ (tableEnvelope C).f1 12846 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12846 164 ∧
    0 ≤ (tableEnvelope C).w1 12846 164 ∧ 0 ≤ (tableEnvelope C).w2 12846 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12846 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12846 164 ∧ 0 ≤ d.f1 12846 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12846 164 ∧ 0 ≤ d.w1 12846 164 ∧ 0 ≤ d.w2 12846 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12846 ≤ 2 * (228 / 100 : ℝ) / 12846 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12846 ≤ 2 * (370 / 100 : ℝ) / 12846 := by
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
    (completeRAData (tableEnvelope C) 12846 164).locationBound 12846 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12846 164).energyBound 12846 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12846 164) (d.f1 12846 164) d.f2 ≤
      32 * (((1113397531 / 250000000000000000) : ℝ) + (297158637 / 200000000000000000) + (178555493 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12846 164) (d.w1 12846 164)
      (d.w2 12846 164) ≤
      32 * (((1771398319 / 100000000000000000000) : ℝ) + (39384879 / 3125000000000000000) + (115121903 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12846 164) (d.f1 12846 164) d.f2 ≤
      ((1113397531 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1113397531 / 250000000000000000)) * ((297158637 / 200000000000000000)) * (126 / 100) +
      2 * (((297158637 / 200000000000000000)) ^ 2 + 2 * ((1113397531 / 250000000000000000)) * ((178555493 / 500000000000000000))) +
      6 * ((297158637 / 200000000000000000)) * ((178555493 / 500000000000000000)) * (126 / 100) + 8 * ((178555493 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12846 164) (d.f1 12846 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12846 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12846 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12846 164) (d.f1 12846 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12846 164) (d.w1 12846 164) (d.w2 12846 164)
  have hwexpr0 : 0 ≤ d.w0 12846 164 + d.w1 12846 164 * √(π / 2) +
      2 * d.w2 12846 164 + energyR16 12846 *
      radiusPolynomialRoot16 (d.w0 12846 164) (d.w1 12846 164) (d.w2 12846 164) := by
    positivity
  constructor
  · change (12846 : ℝ) ^ 8 * (mA 12846 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12846 164) (d.f1 12846 164) d.f2 + locationR16 12846 *
        radiusPolynomialRoot16 (d.f0 12846 164) (d.f1 12846 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12846 : ℝ) ^ 8 * (mA 12846 : ℝ) ^ 8 *
        ((((1113397531 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1113397531 / 250000000000000000)) * ((297158637 / 200000000000000000)) * (126 / 100) +
          2 * (((297158637 / 200000000000000000)) ^ 2 + 2 * ((1113397531 / 250000000000000000)) * ((178555493 / 500000000000000000))) +
          6 * ((297158637 / 200000000000000000)) * ((178555493 / 500000000000000000)) * (126 / 100) + 8 * ((178555493 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12846) *
          (32 * (((1113397531 / 250000000000000000) : ℝ) + (297158637 / 200000000000000000) + (178555493 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12846 : ℝ) ^ 16 *
      (d.w0 12846 164 + d.w1 12846 164 * √(π / 2) + 2 * d.w2 12846 164 +
        energyR16 12846 * radiusPolynomialRoot16 (d.w0 12846 164) (d.w1 12846 164)
          (d.w2 12846 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12846 : ℝ) ^ 16 *
        (((1771398319 / 100000000000000000000) : ℝ) + ((39384879 / 3125000000000000000)) * (126 / 100) + 2 * ((115121903 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12846) *
          (32 * (((1771398319 / 100000000000000000000) : ℝ) + (39384879 / 3125000000000000000) + (115121903 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12846

/-! A coarse bound on the actual paper statistics constant at dimension 12847. -/
namespace BstLean.Part266.Row12847
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12845 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12845 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12845 128 ≤ (13099 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13099 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12847) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12847 : ℕ))
    (by norm_num : (12847 : ℕ) ≤ 16384)
  have ht : paperTail256 12847 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12847 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12847 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12847 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12847 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12847 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12845 128 * √(2 / (12847 : ℝ)) *
      (√(12847 : ℝ) + paperT0 12847 + paperTail256 12847) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12847 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12847 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12847 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12845 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12845 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12847 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12847

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12847
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12847 (61 / 100) 164 (17 / (100 * 12847)) (26 / (10 * 12847)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12847 (61 / 100) 164 (17 / (100 * 12847)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (460375561 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (286682069 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4665345401 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12847 / 12847 * (61 / 100)) ^ 4 * inverseRadius8 (12847 - 1) /
            envelopeGap 12847 (61 / 100) 164 (17 / (100 * 12847)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12847

namespace BstLean.Part266.Row12847
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12847 164 ≤ (178108997 / 40000000000000000)
  f1 : (tableEnvelope C).f1 12847 164 ≤ (148550439 / 100000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (178520767 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12847 164 ≤ (70839399 / 4000000000000000000)
  w1 : (tableEnvelope C).w1 12847 164 ≤ (1260021973 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12847 164 ≤ (460380081 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (460375561 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (460375561 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (286682069 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4665345401 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((454709 / 125000000) : ℝ) ≤ √(17 / (100 * 12847) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12847) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (536409103 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18930203017 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12847) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12847) ≤ (110081231 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12847) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12847 * (164 : ℝ) ^ 2 + 26 / (10 * 12847) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12847) : ℝ)) (tA 12847 * 164 ^ 2 + 26 / (10 * 12847)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((454709 / 125000000))) * ((460375561 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((454709 / 125000000)) ^ 3) * ((286682069 / 200000000000000000000000))) + ((4665345401 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((454709 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12847) : ℝ)) d.D d.V d.P (√(tA 12847) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((454709 / 125000000)) ^ 2 * (((536409103 / 250000000000000)) * ((18930203017 / 500000000000000000)))) + ((4665345401 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12847) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((454709 / 125000000)) * ((460375561 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12847) : ℝ)) (tA 12847 * 164 ^ 2 + 26 / (10 * 12847)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((460375561 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((454709 / 125000000)) ^ 2) * ((286682069 / 200000000000000000000000)) + ((4665345401 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12847) : ℝ)) (√(26 / (10 * 12847) : ℝ)) d.D d.V d.P (√(tA 12847) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((454709 / 125000000)) * (((536409103 / 250000000000000)) * ((18930203017 / 500000000000000000))) + ((4665345401 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12847) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((460375561 / 100000000000000000000) : ℝ) + ((4665345401 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12847

namespace BstLean.Part266.Row12847
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12847 164 ∧
    0 ≤ (tableEnvelope C).f1 12847 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12847 164 ∧
    0 ≤ (tableEnvelope C).w1 12847 164 ∧ 0 ≤ (tableEnvelope C).w2 12847 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12847 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12847 164 ∧ 0 ≤ d.f1 12847 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12847 164 ∧ 0 ≤ d.w1 12847 164 ∧ 0 ≤ d.w2 12847 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12847 ≤ 2 * (228 / 100 : ℝ) / 12847 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12847 ≤ 2 * (370 / 100 : ℝ) / 12847 := by
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
    (completeRAData (tableEnvelope C) 12847 164).locationBound 12847 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12847 164).energyBound 12847 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12847 164) (d.f1 12847 164) d.f2 ≤
      32 * (((178108997 / 40000000000000000) : ℝ) + (148550439 / 100000000000000000) + (178520767 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12847 164) (d.w1 12847 164)
      (d.w2 12847 164) ≤
      32 * (((70839399 / 4000000000000000000) : ℝ) + (1260021973 / 100000000000000000000) + (460380081 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12847 164) (d.f1 12847 164) d.f2 ≤
      ((178108997 / 40000000000000000) : ℝ) ^ 2 + 2 * ((178108997 / 40000000000000000)) * ((148550439 / 100000000000000000)) * (126 / 100) +
      2 * (((148550439 / 100000000000000000)) ^ 2 + 2 * ((178108997 / 40000000000000000)) * ((178520767 / 500000000000000000))) +
      6 * ((148550439 / 100000000000000000)) * ((178520767 / 500000000000000000)) * (126 / 100) + 8 * ((178520767 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12847 164) (d.f1 12847 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12847 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12847 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12847 164) (d.f1 12847 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12847 164) (d.w1 12847 164) (d.w2 12847 164)
  have hwexpr0 : 0 ≤ d.w0 12847 164 + d.w1 12847 164 * √(π / 2) +
      2 * d.w2 12847 164 + energyR16 12847 *
      radiusPolynomialRoot16 (d.w0 12847 164) (d.w1 12847 164) (d.w2 12847 164) := by
    positivity
  constructor
  · change (12847 : ℝ) ^ 8 * (mA 12847 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12847 164) (d.f1 12847 164) d.f2 + locationR16 12847 *
        radiusPolynomialRoot16 (d.f0 12847 164) (d.f1 12847 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12847 : ℝ) ^ 8 * (mA 12847 : ℝ) ^ 8 *
        ((((178108997 / 40000000000000000) : ℝ) ^ 2 + 2 * ((178108997 / 40000000000000000)) * ((148550439 / 100000000000000000)) * (126 / 100) +
          2 * (((148550439 / 100000000000000000)) ^ 2 + 2 * ((178108997 / 40000000000000000)) * ((178520767 / 500000000000000000))) +
          6 * ((148550439 / 100000000000000000)) * ((178520767 / 500000000000000000)) * (126 / 100) + 8 * ((178520767 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12847) *
          (32 * (((178108997 / 40000000000000000) : ℝ) + (148550439 / 100000000000000000) + (178520767 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12847 : ℝ) ^ 16 *
      (d.w0 12847 164 + d.w1 12847 164 * √(π / 2) + 2 * d.w2 12847 164 +
        energyR16 12847 * radiusPolynomialRoot16 (d.w0 12847 164) (d.w1 12847 164)
          (d.w2 12847 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12847 : ℝ) ^ 16 *
        (((70839399 / 4000000000000000000) : ℝ) + ((1260021973 / 100000000000000000000)) * (126 / 100) + 2 * ((460380081 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12847) *
          (32 * (((70839399 / 4000000000000000000) : ℝ) + (1260021973 / 100000000000000000000) + (460380081 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12847

/-! A coarse bound on the actual paper statistics constant at dimension 12848. -/
namespace BstLean.Part266.Row12848
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12846 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12846 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12846 128 ≤ (13100 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13100 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12848) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12848 : ℕ))
    (by norm_num : (12848 : ℕ) ≤ 16384)
  have ht : paperTail256 12848 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12848 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12848 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12848 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12848 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12848 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12846 128 * √(2 / (12848 : ℝ)) *
      (√(12848 : ℝ) + paperT0 12848 + paperTail256 12848) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12848 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12848 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12848 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12846 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12846 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12848 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12848

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12848
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12848 (61 / 100) 164 (17 / (100 * 12848)) (26 / (10 * 12848)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12848 (61 / 100) 164 (17 / (100 * 12848)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (460268067 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1432964113 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (582801659 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12848 / 12848 * (61 / 100)) ^ 4 * inverseRadius8 (12848 - 1) /
            envelopeGap 12848 (61 / 100) 164 (17 / (100 * 12848)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12848

namespace BstLean.Part266.Row12848
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12848 164 ≤ (556482503 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12848 164 ≤ (1485215689 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (178486051 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12848 164 ≤ (885285887 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12848 164 ≤ (1259727917 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12848 164 ≤ (57534073 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (460268067 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (460268067 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1432964113 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (582801659 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((363753 / 100000000) : ℝ) ≤ √(17 / (100 * 12848) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12848) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2145385903 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37854512453 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12848) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12848) ≤ (110072663 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12848) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12848 * (164 : ℝ) ^ 2 + 26 / (10 * 12848) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12848) : ℝ)) (tA 12848 * 164 ^ 2 + 26 / (10 * 12848)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((363753 / 100000000))) * ((460268067 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((363753 / 100000000)) ^ 3) * ((1432964113 / 1000000000000000000000000))) + ((582801659 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((363753 / 100000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12848) : ℝ)) d.D d.V d.P (√(tA 12848) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((363753 / 100000000)) ^ 2 * (((2145385903 / 1000000000000000)) * ((37854512453 / 1000000000000000000)))) + ((582801659 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12848) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((363753 / 100000000)) * ((460268067 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12848) : ℝ)) (tA 12848 * 164 ^ 2 + 26 / (10 * 12848)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((460268067 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((363753 / 100000000)) ^ 2) * ((1432964113 / 1000000000000000000000000)) + ((582801659 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12848) : ℝ)) (√(26 / (10 * 12848) : ℝ)) d.D d.V d.P (√(tA 12848) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((363753 / 100000000)) * (((2145385903 / 1000000000000000)) * ((37854512453 / 1000000000000000000))) + ((582801659 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12848) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((460268067 / 100000000000000000000) : ℝ) + ((582801659 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12848

namespace BstLean.Part266.Row12848
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12848 164 ∧
    0 ≤ (tableEnvelope C).f1 12848 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12848 164 ∧
    0 ≤ (tableEnvelope C).w1 12848 164 ∧ 0 ≤ (tableEnvelope C).w2 12848 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12848 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12848 164 ∧ 0 ≤ d.f1 12848 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12848 164 ∧ 0 ≤ d.w1 12848 164 ∧ 0 ≤ d.w2 12848 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12848 ≤ 2 * (228 / 100 : ℝ) / 12848 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12848 ≤ 2 * (370 / 100 : ℝ) / 12848 := by
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
    (completeRAData (tableEnvelope C) 12848 164).locationBound 12848 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12848 164).energyBound 12848 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12848 164) (d.f1 12848 164) d.f2 ≤
      32 * (((556482503 / 125000000000000000) : ℝ) + (1485215689 / 1000000000000000000) + (178486051 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12848 164) (d.w1 12848 164)
      (d.w2 12848 164) ≤
      32 * (((885285887 / 50000000000000000000) : ℝ) + (1259727917 / 100000000000000000000) + (57534073 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12848 164) (d.f1 12848 164) d.f2 ≤
      ((556482503 / 125000000000000000) : ℝ) ^ 2 + 2 * ((556482503 / 125000000000000000)) * ((1485215689 / 1000000000000000000)) * (126 / 100) +
      2 * (((1485215689 / 1000000000000000000)) ^ 2 + 2 * ((556482503 / 125000000000000000)) * ((178486051 / 500000000000000000))) +
      6 * ((1485215689 / 1000000000000000000)) * ((178486051 / 500000000000000000)) * (126 / 100) + 8 * ((178486051 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12848 164) (d.f1 12848 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12848 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12848 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12848 164) (d.f1 12848 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12848 164) (d.w1 12848 164) (d.w2 12848 164)
  have hwexpr0 : 0 ≤ d.w0 12848 164 + d.w1 12848 164 * √(π / 2) +
      2 * d.w2 12848 164 + energyR16 12848 *
      radiusPolynomialRoot16 (d.w0 12848 164) (d.w1 12848 164) (d.w2 12848 164) := by
    positivity
  constructor
  · change (12848 : ℝ) ^ 8 * (mA 12848 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12848 164) (d.f1 12848 164) d.f2 + locationR16 12848 *
        radiusPolynomialRoot16 (d.f0 12848 164) (d.f1 12848 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12848 : ℝ) ^ 8 * (mA 12848 : ℝ) ^ 8 *
        ((((556482503 / 125000000000000000) : ℝ) ^ 2 + 2 * ((556482503 / 125000000000000000)) * ((1485215689 / 1000000000000000000)) * (126 / 100) +
          2 * (((1485215689 / 1000000000000000000)) ^ 2 + 2 * ((556482503 / 125000000000000000)) * ((178486051 / 500000000000000000))) +
          6 * ((1485215689 / 1000000000000000000)) * ((178486051 / 500000000000000000)) * (126 / 100) + 8 * ((178486051 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12848) *
          (32 * (((556482503 / 125000000000000000) : ℝ) + (1485215689 / 1000000000000000000) + (178486051 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12848 : ℝ) ^ 16 *
      (d.w0 12848 164 + d.w1 12848 164 * √(π / 2) + 2 * d.w2 12848 164 +
        energyR16 12848 * radiusPolynomialRoot16 (d.w0 12848 164) (d.w1 12848 164)
          (d.w2 12848 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12848 : ℝ) ^ 16 *
        (((885285887 / 50000000000000000000) : ℝ) + ((1259727917 / 100000000000000000000)) * (126 / 100) + 2 * ((57534073 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12848) *
          (32 * (((885285887 / 50000000000000000000) : ℝ) + (1259727917 / 100000000000000000000) + (57534073 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12848

/-! A coarse bound on the actual paper statistics constant at dimension 12849. -/
namespace BstLean.Part266.Row12849
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12847 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12847 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12847 128 ≤ (13101 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13101 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12849) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12849 : ℕ))
    (by norm_num : (12849 : ℕ) ≤ 16384)
  have ht : paperTail256 12849 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12849 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12849 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12849 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12849 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12849 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12847 128 * √(2 / (12849 : ℝ)) *
      (√(12849 : ℝ) + paperT0 12849 + paperTail256 12849) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12849 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12849 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12849 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12847 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12847 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12849 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12849

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12849
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12849 (61 / 100) 164 (17 / (100 * 12849)) (26 / (10 * 12849)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12849 (61 / 100) 164 (17 / (100 * 12849)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (92032121 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (716259027 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4659483219 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12849 / 12849 * (61 / 100)) ^ 4 * inverseRadius8 (12849 - 1) /
            envelopeGap 12849 (61 / 100) 164 (17 / (100 * 12849)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12849

namespace BstLean.Part266.Row12849
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12849 164 ≤ (2225495941 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12849 164 ≤ (74246313 / 50000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (5576603 / 15625000000000000)
  w0 : (tableEnvelope C).w0 12849 164 ≤ (177015799 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 12849 164 ≤ (1259433609 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12849 164 ≤ (460165119 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (92032121 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (92032121 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (716259027 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4659483219 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3637389 / 1000000000) : ℝ) ≤ √(17 / (100 * 12849) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12849) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2145135439 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (473107753 / 12500000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12849) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12849) ≤ (3439503 / 31250000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12849) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12849 * (164 : ℝ) ^ 2 + 26 / (10 * 12849) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12849) : ℝ)) (tA 12849 * 164 ^ 2 + 26 / (10 * 12849)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3637389 / 1000000000))) * ((92032121 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3637389 / 1000000000)) ^ 3) * ((716259027 / 500000000000000000000000))) + ((4659483219 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3637389 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12849) : ℝ)) d.D d.V d.P (√(tA 12849) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3637389 / 1000000000)) ^ 2 * (((2145135439 / 1000000000000000)) * ((473107753 / 12500000000000000)))) + ((4659483219 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12849) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3637389 / 1000000000)) * ((92032121 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12849) : ℝ)) (tA 12849 * 164 ^ 2 + 26 / (10 * 12849)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((92032121 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3637389 / 1000000000)) ^ 2) * ((716259027 / 500000000000000000000000)) + ((4659483219 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12849) : ℝ)) (√(26 / (10 * 12849) : ℝ)) d.D d.V d.P (√(tA 12849) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3637389 / 1000000000)) * (((2145135439 / 1000000000000000)) * ((473107753 / 12500000000000000))) + ((4659483219 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12849) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((92032121 / 20000000000000000000) : ℝ) + ((4659483219 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12849

namespace BstLean.Part266.Row12849
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12849 164 ∧
    0 ≤ (tableEnvelope C).f1 12849 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12849 164 ∧
    0 ≤ (tableEnvelope C).w1 12849 164 ∧ 0 ≤ (tableEnvelope C).w2 12849 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12849 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12849 164 ∧ 0 ≤ d.f1 12849 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12849 164 ∧ 0 ≤ d.w1 12849 164 ∧ 0 ≤ d.w2 12849 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12849 ≤ 2 * (228 / 100 : ℝ) / 12849 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12849 ≤ 2 * (370 / 100 : ℝ) / 12849 := by
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
    (completeRAData (tableEnvelope C) 12849 164).locationBound 12849 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12849 164).energyBound 12849 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12849 164) (d.f1 12849 164) d.f2 ≤
      32 * (((2225495941 / 500000000000000000) : ℝ) + (74246313 / 50000000000000000) + (5576603 / 15625000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12849 164) (d.w1 12849 164)
      (d.w2 12849 164) ≤
      32 * (((177015799 / 10000000000000000000) : ℝ) + (1259433609 / 100000000000000000000) + (460165119 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12849 164) (d.f1 12849 164) d.f2 ≤
      ((2225495941 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2225495941 / 500000000000000000)) * ((74246313 / 50000000000000000)) * (126 / 100) +
      2 * (((74246313 / 50000000000000000)) ^ 2 + 2 * ((2225495941 / 500000000000000000)) * ((5576603 / 15625000000000000))) +
      6 * ((74246313 / 50000000000000000)) * ((5576603 / 15625000000000000)) * (126 / 100) + 8 * ((5576603 / 15625000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12849 164) (d.f1 12849 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12849 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12849 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12849 164) (d.f1 12849 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12849 164) (d.w1 12849 164) (d.w2 12849 164)
  have hwexpr0 : 0 ≤ d.w0 12849 164 + d.w1 12849 164 * √(π / 2) +
      2 * d.w2 12849 164 + energyR16 12849 *
      radiusPolynomialRoot16 (d.w0 12849 164) (d.w1 12849 164) (d.w2 12849 164) := by
    positivity
  constructor
  · change (12849 : ℝ) ^ 8 * (mA 12849 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12849 164) (d.f1 12849 164) d.f2 + locationR16 12849 *
        radiusPolynomialRoot16 (d.f0 12849 164) (d.f1 12849 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12849 : ℝ) ^ 8 * (mA 12849 : ℝ) ^ 8 *
        ((((2225495941 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2225495941 / 500000000000000000)) * ((74246313 / 50000000000000000)) * (126 / 100) +
          2 * (((74246313 / 50000000000000000)) ^ 2 + 2 * ((2225495941 / 500000000000000000)) * ((5576603 / 15625000000000000))) +
          6 * ((74246313 / 50000000000000000)) * ((5576603 / 15625000000000000)) * (126 / 100) + 8 * ((5576603 / 15625000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12849) *
          (32 * (((2225495941 / 500000000000000000) : ℝ) + (74246313 / 50000000000000000) + (5576603 / 15625000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12849 : ℝ) ^ 16 *
      (d.w0 12849 164 + d.w1 12849 164 * √(π / 2) + 2 * d.w2 12849 164 +
        energyR16 12849 * radiusPolynomialRoot16 (d.w0 12849 164) (d.w1 12849 164)
          (d.w2 12849 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12849 : ℝ) ^ 16 *
        (((177015799 / 10000000000000000000) : ℝ) + ((1259433609 / 100000000000000000000)) * (126 / 100) + 2 * ((460165119 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12849) *
          (32 * (((177015799 / 10000000000000000000) : ℝ) + (1259433609 / 100000000000000000000) + (460165119 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12849
