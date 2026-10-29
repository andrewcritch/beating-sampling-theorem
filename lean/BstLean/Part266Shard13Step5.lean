import BstLean.Part266Shard13Step4


/-! A coarse bound on the actual paper statistics constant at dimension 12675. -/
namespace BstLean.Part266.Row12675
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12673 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12673 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12673 128 ≤ (12927 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12927 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12675) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12675 : ℕ))
    (by norm_num : (12675 : ℕ) ≤ 16384)
  have ht : paperTail256 12675 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12675 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12675 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12675 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12675 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12675 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12673 128 * √(2 / (12675 : ℝ)) *
      (√(12675 : ℝ) + paperT0 12675 + paperTail256 12675) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12675 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12675 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12675 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12673 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12673 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12675 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12675

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12675
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12675 (61 / 100) 163 (17 / (100 * 12675)) (26 / (10 * 12675)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12675 (61 / 100) 163 (17 / (100 * 12675)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (479373969 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1512817281 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (40621617 / 7812500000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12675 / 12675 * (61 / 100)) ^ 4 * inverseRadius8 (12675 - 1) /
            envelopeGap 12675 (61 / 100) 163 (17 / (100 * 12675)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12675

namespace BstLean.Part266.Row12675
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12675 163 ≤ (1151334047 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12675 163 ≤ (192052243 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (46159821 / 125000000000000000)
  w0 : (tableEnvelope C).w0 12675 163 ≤ (368813797 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12675 163 ≤ (1312019767 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12675 163 ≤ (239689503 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (479373969 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (479373969 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1512817281 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (40621617 / 7812500000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((366227 / 100000000) : ℝ) ≤ √(17 / (100 * 12675) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12675) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2189461051 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38894951871 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12675) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12675) ≤ (22315007 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12675) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12675 * (163 : ℝ) ^ 2 + 26 / (10 * 12675) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12675) : ℝ)) (tA 12675 * 163 ^ 2 + 26 / (10 * 12675)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((366227 / 100000000))) * ((479373969 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((366227 / 100000000)) ^ 3) * ((1512817281 / 1000000000000000000000000))) + ((40621617 / 7812500000000000000000)) * (3 / 2 * (39895 / 100000) / ((366227 / 100000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12675) : ℝ)) d.D d.V d.P (√(tA 12675) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((366227 / 100000000)) ^ 2 * (((2189461051 / 1000000000000000)) * ((38894951871 / 1000000000000000000)))) + ((40621617 / 7812500000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12675) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((366227 / 100000000)) * ((479373969 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12675) : ℝ)) (tA 12675 * 163 ^ 2 + 26 / (10 * 12675)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((479373969 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((366227 / 100000000)) ^ 2) * ((1512817281 / 1000000000000000000000000)) + ((40621617 / 7812500000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12675) : ℝ)) (√(26 / (10 * 12675) : ℝ)) d.D d.V d.P (√(tA 12675) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((366227 / 100000000)) * (((2189461051 / 1000000000000000)) * ((38894951871 / 1000000000000000000))) + ((40621617 / 7812500000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12675) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((479373969 / 100000000000000000000) : ℝ) + ((40621617 / 7812500000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12675

namespace BstLean.Part266.Row12675
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12675 163 ∧
    0 ≤ (tableEnvelope C).f1 12675 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12675 163 ∧
    0 ≤ (tableEnvelope C).w1 12675 163 ∧ 0 ≤ (tableEnvelope C).w2 12675 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12675 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12675 163 ∧ 0 ≤ d.f1 12675 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12675 163 ∧ 0 ≤ d.w1 12675 163 ∧ 0 ≤ d.w2 12675 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12675 ≤ 2 * (228 / 100 : ℝ) / 12675 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12675 ≤ 2 * (370 / 100 : ℝ) / 12675 := by
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
    (completeRAData (tableEnvelope C) 12675 163).locationBound 12675 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12675 163).energyBound 12675 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12675 163) (d.f1 12675 163) d.f2 ≤
      32 * (((1151334047 / 250000000000000000) : ℝ) + (192052243 / 125000000000000000) + (46159821 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12675 163) (d.w1 12675 163)
      (d.w2 12675 163) ≤
      32 * (((368813797 / 20000000000000000000) : ℝ) + (1312019767 / 100000000000000000000) + (239689503 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12675 163) (d.f1 12675 163) d.f2 ≤
      ((1151334047 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1151334047 / 250000000000000000)) * ((192052243 / 125000000000000000)) * (126 / 100) +
      2 * (((192052243 / 125000000000000000)) ^ 2 + 2 * ((1151334047 / 250000000000000000)) * ((46159821 / 125000000000000000))) +
      6 * ((192052243 / 125000000000000000)) * ((46159821 / 125000000000000000)) * (126 / 100) + 8 * ((46159821 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12675 163) (d.f1 12675 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12675 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12675 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12675 163) (d.f1 12675 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12675 163) (d.w1 12675 163) (d.w2 12675 163)
  have hwexpr0 : 0 ≤ d.w0 12675 163 + d.w1 12675 163 * √(π / 2) +
      2 * d.w2 12675 163 + energyR16 12675 *
      radiusPolynomialRoot16 (d.w0 12675 163) (d.w1 12675 163) (d.w2 12675 163) := by
    positivity
  constructor
  · change (12675 : ℝ) ^ 8 * (mA 12675 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12675 163) (d.f1 12675 163) d.f2 + locationR16 12675 *
        radiusPolynomialRoot16 (d.f0 12675 163) (d.f1 12675 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12675 : ℝ) ^ 8 * (mA 12675 : ℝ) ^ 8 *
        ((((1151334047 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1151334047 / 250000000000000000)) * ((192052243 / 125000000000000000)) * (126 / 100) +
          2 * (((192052243 / 125000000000000000)) ^ 2 + 2 * ((1151334047 / 250000000000000000)) * ((46159821 / 125000000000000000))) +
          6 * ((192052243 / 125000000000000000)) * ((46159821 / 125000000000000000)) * (126 / 100) + 8 * ((46159821 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12675) *
          (32 * (((1151334047 / 250000000000000000) : ℝ) + (192052243 / 125000000000000000) + (46159821 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12675 : ℝ) ^ 16 *
      (d.w0 12675 163 + d.w1 12675 163 * √(π / 2) + 2 * d.w2 12675 163 +
        energyR16 12675 * radiusPolynomialRoot16 (d.w0 12675 163) (d.w1 12675 163)
          (d.w2 12675 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12675 : ℝ) ^ 16 *
        (((368813797 / 20000000000000000000) : ℝ) + ((1312019767 / 100000000000000000000)) * (126 / 100) + 2 * ((239689503 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12675) *
          (32 * (((368813797 / 20000000000000000000) : ℝ) + (1312019767 / 100000000000000000000) + (239689503 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12675

/-! A coarse bound on the actual paper statistics constant at dimension 12676. -/
namespace BstLean.Part266.Row12676
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12674 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12674 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12674 128 ≤ (12928 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12928 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12676) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12676 : ℕ))
    (by norm_num : (12676 : ℕ) ≤ 16384)
  have ht : paperTail256 12676 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12676 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12676 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12676 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12676 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12676 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12674 128 * √(2 / (12676 : ℝ)) *
      (√(12676 : ℝ) + paperT0 12676 + paperTail256 12676) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12676 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12676 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12676 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12674 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12674 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12676 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12676

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12676
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12676 (61 / 100) 163 (17 / (100 * 12676)) (26 / (10 * 12676)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12676 (61 / 100) 163 (17 / (100 * 12676)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (11981513 / 2500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1512339939 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1039250859 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12676 / 12676 * (61 / 100)) ^ 4 * inverseRadius8 (12676 - 1) /
            envelopeGap 12676 (61 / 100) 163 (17 / (100 * 12676)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12676

namespace BstLean.Part266.Row12676
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12676 163 ≤ (4604426239 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12676 163 ≤ (76805727 / 50000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (92301423 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12676 163 ≤ (1843632223 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12676 163 ≤ (655854549 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12676 163 ≤ (239632777 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (11981513 / 2500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (11981513 / 2500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1512339939 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1039250859 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1831063 / 500000000) : ℝ) ≤ √(17 / (100 * 12676) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12676) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (547300489 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38888815089 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12676) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12676) ≤ (111566233 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12676) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12676 * (163 : ℝ) ^ 2 + 26 / (10 * 12676) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12676) : ℝ)) (tA 12676 * 163 ^ 2 + 26 / (10 * 12676)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1831063 / 500000000))) * ((11981513 / 2500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1831063 / 500000000)) ^ 3) * ((1512339939 / 1000000000000000000000000))) + ((1039250859 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1831063 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12676) : ℝ)) d.D d.V d.P (√(tA 12676) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1831063 / 500000000)) ^ 2 * (((547300489 / 250000000000000)) * ((38888815089 / 1000000000000000000)))) + ((1039250859 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12676) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1831063 / 500000000)) * ((11981513 / 2500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12676) : ℝ)) (tA 12676 * 163 ^ 2 + 26 / (10 * 12676)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((11981513 / 2500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1831063 / 500000000)) ^ 2) * ((1512339939 / 1000000000000000000000000)) + ((1039250859 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12676) : ℝ)) (√(26 / (10 * 12676) : ℝ)) d.D d.V d.P (√(tA 12676) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1831063 / 500000000)) * (((547300489 / 250000000000000)) * ((38888815089 / 1000000000000000000))) + ((1039250859 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12676) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((11981513 / 2500000000000000000) : ℝ) + ((1039250859 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12676

namespace BstLean.Part266.Row12676
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12676 163 ∧
    0 ≤ (tableEnvelope C).f1 12676 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12676 163 ∧
    0 ≤ (tableEnvelope C).w1 12676 163 ∧ 0 ≤ (tableEnvelope C).w2 12676 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12676 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12676 163 ∧ 0 ≤ d.f1 12676 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12676 163 ∧ 0 ≤ d.w1 12676 163 ∧ 0 ≤ d.w2 12676 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12676 ≤ 2 * (228 / 100 : ℝ) / 12676 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12676 ≤ 2 * (370 / 100 : ℝ) / 12676 := by
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
    (completeRAData (tableEnvelope C) 12676 163).locationBound 12676 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12676 163).energyBound 12676 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12676 163) (d.f1 12676 163) d.f2 ≤
      32 * (((4604426239 / 1000000000000000000) : ℝ) + (76805727 / 50000000000000000) + (92301423 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12676 163) (d.w1 12676 163)
      (d.w2 12676 163) ≤
      32 * (((1843632223 / 100000000000000000000) : ℝ) + (655854549 / 50000000000000000000) + (239632777 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12676 163) (d.f1 12676 163) d.f2 ≤
      ((4604426239 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4604426239 / 1000000000000000000)) * ((76805727 / 50000000000000000)) * (126 / 100) +
      2 * (((76805727 / 50000000000000000)) ^ 2 + 2 * ((4604426239 / 1000000000000000000)) * ((92301423 / 250000000000000000))) +
      6 * ((76805727 / 50000000000000000)) * ((92301423 / 250000000000000000)) * (126 / 100) + 8 * ((92301423 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12676 163) (d.f1 12676 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12676 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12676 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12676 163) (d.f1 12676 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12676 163) (d.w1 12676 163) (d.w2 12676 163)
  have hwexpr0 : 0 ≤ d.w0 12676 163 + d.w1 12676 163 * √(π / 2) +
      2 * d.w2 12676 163 + energyR16 12676 *
      radiusPolynomialRoot16 (d.w0 12676 163) (d.w1 12676 163) (d.w2 12676 163) := by
    positivity
  constructor
  · change (12676 : ℝ) ^ 8 * (mA 12676 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12676 163) (d.f1 12676 163) d.f2 + locationR16 12676 *
        radiusPolynomialRoot16 (d.f0 12676 163) (d.f1 12676 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12676 : ℝ) ^ 8 * (mA 12676 : ℝ) ^ 8 *
        ((((4604426239 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4604426239 / 1000000000000000000)) * ((76805727 / 50000000000000000)) * (126 / 100) +
          2 * (((76805727 / 50000000000000000)) ^ 2 + 2 * ((4604426239 / 1000000000000000000)) * ((92301423 / 250000000000000000))) +
          6 * ((76805727 / 50000000000000000)) * ((92301423 / 250000000000000000)) * (126 / 100) + 8 * ((92301423 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12676) *
          (32 * (((4604426239 / 1000000000000000000) : ℝ) + (76805727 / 50000000000000000) + (92301423 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12676 : ℝ) ^ 16 *
      (d.w0 12676 163 + d.w1 12676 163 * √(π / 2) + 2 * d.w2 12676 163 +
        energyR16 12676 * radiusPolynomialRoot16 (d.w0 12676 163) (d.w1 12676 163)
          (d.w2 12676 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12676 : ℝ) ^ 16 *
        (((1843632223 / 100000000000000000000) : ℝ) + ((655854549 / 50000000000000000000)) * (126 / 100) + 2 * ((239632777 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12676) *
          (32 * (((1843632223 / 100000000000000000000) : ℝ) + (655854549 / 50000000000000000000) + (239632777 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12676

/-! A coarse bound on the actual paper statistics constant at dimension 12677. -/
namespace BstLean.Part266.Row12677
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12675 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12675 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12675 128 ≤ (12929 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12929 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12677) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12677 : ℕ))
    (by norm_num : (12677 : ℕ) ≤ 16384)
  have ht : paperTail256 12677 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12677 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12677 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12677 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12677 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12677 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12675 128 * √(2 / (12677 : ℝ)) *
      (√(12677 : ℝ) + paperT0 12677 + paperTail256 12677) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12677 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12677 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12677 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12675 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12675 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12677 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12677

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12677
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12677 (61 / 100) 163 (17 / (100 * 12677)) (26 / (10 * 12677)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12677 (61 / 100) 163 (17 / (100 * 12677)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (239573553 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (302372557 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (519294399 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12677 / 12677 * (61 / 100)) ^ 4 * inverseRadius8 (12677 - 1) /
            envelopeGap 12677 (61 / 100) 163 (17 / (100 * 12677)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12677

namespace BstLean.Part266.Row12677
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12677 163 ≤ (4603516601 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12677 163 ≤ (1535811233 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (92283209 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12677 163 ≤ (184319561 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 12677 163 ≤ (327849633 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12677 163 ≤ (479152137 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (239573553 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (239573553 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (302372557 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (519294399 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1830991 / 500000000) : ℝ) ≤ √(17 / (100 * 12677) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12677) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (218894291 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9720669939 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12677) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12677) ≤ (13944679 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12677) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12677 * (163 : ℝ) ^ 2 + 26 / (10 * 12677) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12677) : ℝ)) (tA 12677 * 163 ^ 2 + 26 / (10 * 12677)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1830991 / 500000000))) * ((239573553 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1830991 / 500000000)) ^ 3) * ((302372557 / 200000000000000000000000))) + ((519294399 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1830991 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12677) : ℝ)) d.D d.V d.P (√(tA 12677) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1830991 / 500000000)) ^ 2 * (((218894291 / 100000000000000)) * ((9720669939 / 250000000000000000)))) + ((519294399 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12677) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1830991 / 500000000)) * ((239573553 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12677) : ℝ)) (tA 12677 * 163 ^ 2 + 26 / (10 * 12677)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((239573553 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1830991 / 500000000)) ^ 2) * ((302372557 / 200000000000000000000000)) + ((519294399 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12677) : ℝ)) (√(26 / (10 * 12677) : ℝ)) d.D d.V d.P (√(tA 12677) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1830991 / 500000000)) * (((218894291 / 100000000000000)) * ((9720669939 / 250000000000000000))) + ((519294399 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12677) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((239573553 / 50000000000000000000) : ℝ) + ((519294399 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12677

namespace BstLean.Part266.Row12677
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12677 163 ∧
    0 ≤ (tableEnvelope C).f1 12677 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12677 163 ∧
    0 ≤ (tableEnvelope C).w1 12677 163 ∧ 0 ≤ (tableEnvelope C).w2 12677 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12677 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12677 163 ∧ 0 ≤ d.f1 12677 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12677 163 ∧ 0 ≤ d.w1 12677 163 ∧ 0 ≤ d.w2 12677 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12677 ≤ 2 * (228 / 100 : ℝ) / 12677 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12677 ≤ 2 * (370 / 100 : ℝ) / 12677 := by
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
    (completeRAData (tableEnvelope C) 12677 163).locationBound 12677 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12677 163).energyBound 12677 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12677 163) (d.f1 12677 163) d.f2 ≤
      32 * (((4603516601 / 1000000000000000000) : ℝ) + (1535811233 / 1000000000000000000) + (92283209 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12677 163) (d.w1 12677 163)
      (d.w2 12677 163) ≤
      32 * (((184319561 / 10000000000000000000) : ℝ) + (327849633 / 25000000000000000000) + (479152137 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12677 163) (d.f1 12677 163) d.f2 ≤
      ((4603516601 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4603516601 / 1000000000000000000)) * ((1535811233 / 1000000000000000000)) * (126 / 100) +
      2 * (((1535811233 / 1000000000000000000)) ^ 2 + 2 * ((4603516601 / 1000000000000000000)) * ((92283209 / 250000000000000000))) +
      6 * ((1535811233 / 1000000000000000000)) * ((92283209 / 250000000000000000)) * (126 / 100) + 8 * ((92283209 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12677 163) (d.f1 12677 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12677 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12677 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12677 163) (d.f1 12677 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12677 163) (d.w1 12677 163) (d.w2 12677 163)
  have hwexpr0 : 0 ≤ d.w0 12677 163 + d.w1 12677 163 * √(π / 2) +
      2 * d.w2 12677 163 + energyR16 12677 *
      radiusPolynomialRoot16 (d.w0 12677 163) (d.w1 12677 163) (d.w2 12677 163) := by
    positivity
  constructor
  · change (12677 : ℝ) ^ 8 * (mA 12677 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12677 163) (d.f1 12677 163) d.f2 + locationR16 12677 *
        radiusPolynomialRoot16 (d.f0 12677 163) (d.f1 12677 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12677 : ℝ) ^ 8 * (mA 12677 : ℝ) ^ 8 *
        ((((4603516601 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4603516601 / 1000000000000000000)) * ((1535811233 / 1000000000000000000)) * (126 / 100) +
          2 * (((1535811233 / 1000000000000000000)) ^ 2 + 2 * ((4603516601 / 1000000000000000000)) * ((92283209 / 250000000000000000))) +
          6 * ((1535811233 / 1000000000000000000)) * ((92283209 / 250000000000000000)) * (126 / 100) + 8 * ((92283209 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12677) *
          (32 * (((4603516601 / 1000000000000000000) : ℝ) + (1535811233 / 1000000000000000000) + (92283209 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12677 : ℝ) ^ 16 *
      (d.w0 12677 163 + d.w1 12677 163 * √(π / 2) + 2 * d.w2 12677 163 +
        energyR16 12677 * radiusPolynomialRoot16 (d.w0 12677 163) (d.w1 12677 163)
          (d.w2 12677 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12677 : ℝ) ^ 16 *
        (((184319561 / 10000000000000000000) : ℝ) + ((327849633 / 25000000000000000000)) * (126 / 100) + 2 * ((479152137 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12677) *
          (32 * (((184319561 / 10000000000000000000) : ℝ) + (327849633 / 25000000000000000000) + (479152137 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12677

/-! A coarse bound on the actual paper statistics constant at dimension 12678. -/
namespace BstLean.Part266.Row12678
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12676 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12676 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12676 128 ≤ (12930 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12930 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12678) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12678 : ℕ))
    (by norm_num : (12678 : ℕ) ≤ 16384)
  have ht : paperTail256 12678 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12678 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12678 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12678 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12678 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12678 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12676 128 * √(2 / (12678 : ℝ)) *
      (√(12678 : ℝ) + paperT0 12678 + paperTail256 12678) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12678 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12678 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12678 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12676 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12676 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12678 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12678

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12678
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12678 (61 / 100) 163 (17 / (100 * 12678)) (26 / (10 * 12678)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12678 (61 / 100) 163 (17 / (100 * 12678)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (3742451 / 781250000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1511385819 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5189636059 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12678 / 12678 * (61 / 100)) ^ 4 * inverseRadius8 (12678 - 1) /
            envelopeGap 12678 (61 / 100) 163 (17 / (100 * 12678)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12678

namespace BstLean.Part266.Row12678
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12678 163 ≤ (920522181 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12678 163 ≤ (11996163 / 7812500000000000)
  f2 : (tableEnvelope C).f2 ≤ (46132513 / 125000000000000000)
  w0 : (tableEnvelope C).w0 12678 163 ≤ (460689973 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12678 163 ≤ (1311088429 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12678 163 ≤ (119759689 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (3742451 / 781250000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (3742451 / 781250000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1511385819 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5189636059 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3661837 / 1000000000) : ℝ) ≤ √(17 / (100 * 12678) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12678) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (547170979 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38876545873 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12678) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12678) ≤ (111548633 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12678) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12678 * (163 : ℝ) ^ 2 + 26 / (10 * 12678) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12678) : ℝ)) (tA 12678 * 163 ^ 2 + 26 / (10 * 12678)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3661837 / 1000000000))) * ((3742451 / 781250000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3661837 / 1000000000)) ^ 3) * ((1511385819 / 1000000000000000000000000))) + ((5189636059 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3661837 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12678) : ℝ)) d.D d.V d.P (√(tA 12678) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3661837 / 1000000000)) ^ 2 * (((547170979 / 250000000000000)) * ((38876545873 / 1000000000000000000)))) + ((5189636059 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12678) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3661837 / 1000000000)) * ((3742451 / 781250000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12678) : ℝ)) (tA 12678 * 163 ^ 2 + 26 / (10 * 12678)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((3742451 / 781250000000000000) : ℝ) + (24198 / 100000) / (2 * ((3661837 / 1000000000)) ^ 2) * ((1511385819 / 1000000000000000000000000)) + ((5189636059 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12678) : ℝ)) (√(26 / (10 * 12678) : ℝ)) d.D d.V d.P (√(tA 12678) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3661837 / 1000000000)) * (((547170979 / 250000000000000)) * ((38876545873 / 1000000000000000000))) + ((5189636059 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12678) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((3742451 / 781250000000000000) : ℝ) + ((5189636059 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12678

namespace BstLean.Part266.Row12678
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12678 163 ∧
    0 ≤ (tableEnvelope C).f1 12678 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12678 163 ∧
    0 ≤ (tableEnvelope C).w1 12678 163 ∧ 0 ≤ (tableEnvelope C).w2 12678 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12678 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12678 163 ∧ 0 ≤ d.f1 12678 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12678 163 ∧ 0 ≤ d.w1 12678 163 ∧ 0 ≤ d.w2 12678 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12678 ≤ 2 * (228 / 100 : ℝ) / 12678 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12678 ≤ 2 * (370 / 100 : ℝ) / 12678 := by
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
    (completeRAData (tableEnvelope C) 12678 163).locationBound 12678 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12678 163).energyBound 12678 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12678 163) (d.f1 12678 163) d.f2 ≤
      32 * (((920522181 / 200000000000000000) : ℝ) + (11996163 / 7812500000000000) + (46132513 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12678 163) (d.w1 12678 163)
      (d.w2 12678 163) ≤
      32 * (((460689973 / 25000000000000000000) : ℝ) + (1311088429 / 100000000000000000000) + (119759689 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12678 163) (d.f1 12678 163) d.f2 ≤
      ((920522181 / 200000000000000000) : ℝ) ^ 2 + 2 * ((920522181 / 200000000000000000)) * ((11996163 / 7812500000000000)) * (126 / 100) +
      2 * (((11996163 / 7812500000000000)) ^ 2 + 2 * ((920522181 / 200000000000000000)) * ((46132513 / 125000000000000000))) +
      6 * ((11996163 / 7812500000000000)) * ((46132513 / 125000000000000000)) * (126 / 100) + 8 * ((46132513 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12678 163) (d.f1 12678 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12678 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12678 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12678 163) (d.f1 12678 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12678 163) (d.w1 12678 163) (d.w2 12678 163)
  have hwexpr0 : 0 ≤ d.w0 12678 163 + d.w1 12678 163 * √(π / 2) +
      2 * d.w2 12678 163 + energyR16 12678 *
      radiusPolynomialRoot16 (d.w0 12678 163) (d.w1 12678 163) (d.w2 12678 163) := by
    positivity
  constructor
  · change (12678 : ℝ) ^ 8 * (mA 12678 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12678 163) (d.f1 12678 163) d.f2 + locationR16 12678 *
        radiusPolynomialRoot16 (d.f0 12678 163) (d.f1 12678 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12678 : ℝ) ^ 8 * (mA 12678 : ℝ) ^ 8 *
        ((((920522181 / 200000000000000000) : ℝ) ^ 2 + 2 * ((920522181 / 200000000000000000)) * ((11996163 / 7812500000000000)) * (126 / 100) +
          2 * (((11996163 / 7812500000000000)) ^ 2 + 2 * ((920522181 / 200000000000000000)) * ((46132513 / 125000000000000000))) +
          6 * ((11996163 / 7812500000000000)) * ((46132513 / 125000000000000000)) * (126 / 100) + 8 * ((46132513 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12678) *
          (32 * (((920522181 / 200000000000000000) : ℝ) + (11996163 / 7812500000000000) + (46132513 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12678 : ℝ) ^ 16 *
      (d.w0 12678 163 + d.w1 12678 163 * √(π / 2) + 2 * d.w2 12678 163 +
        energyR16 12678 * radiusPolynomialRoot16 (d.w0 12678 163) (d.w1 12678 163)
          (d.w2 12678 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12678 : ℝ) ^ 16 *
        (((460689973 / 25000000000000000000) : ℝ) + ((1311088429 / 100000000000000000000)) * (126 / 100) + 2 * ((119759689 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12678) *
          (32 * (((460689973 / 25000000000000000000) : ℝ) + (1311088429 / 100000000000000000000) + (119759689 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12678

/-! A coarse bound on the actual paper statistics constant at dimension 12679. -/
namespace BstLean.Part266.Row12679
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12677 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12677 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12677 128 ≤ (12931 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12931 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12679) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12679 : ℕ))
    (by norm_num : (12679 : ℕ) ≤ 16384)
  have ht : paperTail256 12679 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12679 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12679 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12679 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12679 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12679 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12677 128 * √(2 / (12679 : ℝ)) *
      (√(12679 : ℝ) + paperT0 12679 + paperTail256 12679) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12679 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12679 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12679 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12677 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12677 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12679 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12679

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12679
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12679 (61 / 100) 163 (17 / (100 * 12679)) (26 / (10 * 12679)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12679 (61 / 100) 163 (17 / (100 * 12679)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (239460193 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1510909041 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2593165251 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12679 / 12679 * (61 / 100)) ^ 4 * inverseRadius8 (12679 - 1) /
            envelopeGap 12679 (61 / 100) 163 (17 / (100 * 12679)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12679

namespace BstLean.Part266.Row12679
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12679 163 ≤ (4601701893 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12679 163 ≤ (1535205753 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (92246823 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12679 163 ≤ (1842323581 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12679 163 ≤ (1310778071 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12679 163 ≤ (47892541 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (239460193 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (239460193 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1510909041 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2593165251 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3661693 / 1000000000) : ℝ) ≤ √(17 / (100 * 12679) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12679) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2188424973 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38870413441 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12679) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12679) ≤ (22307967 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12679) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12679 * (163 : ℝ) ^ 2 + 26 / (10 * 12679) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12679) : ℝ)) (tA 12679 * 163 ^ 2 + 26 / (10 * 12679)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3661693 / 1000000000))) * ((239460193 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3661693 / 1000000000)) ^ 3) * ((1510909041 / 1000000000000000000000000))) + ((2593165251 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3661693 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12679) : ℝ)) d.D d.V d.P (√(tA 12679) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3661693 / 1000000000)) ^ 2 * (((2188424973 / 1000000000000000)) * ((38870413441 / 1000000000000000000)))) + ((2593165251 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12679) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3661693 / 1000000000)) * ((239460193 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12679) : ℝ)) (tA 12679 * 163 ^ 2 + 26 / (10 * 12679)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((239460193 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3661693 / 1000000000)) ^ 2) * ((1510909041 / 1000000000000000000000000)) + ((2593165251 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12679) : ℝ)) (√(26 / (10 * 12679) : ℝ)) d.D d.V d.P (√(tA 12679) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3661693 / 1000000000)) * (((2188424973 / 1000000000000000)) * ((38870413441 / 1000000000000000000))) + ((2593165251 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12679) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((239460193 / 50000000000000000000) : ℝ) + ((2593165251 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12679

namespace BstLean.Part266.Row12679
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12679 163 ∧
    0 ≤ (tableEnvelope C).f1 12679 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12679 163 ∧
    0 ≤ (tableEnvelope C).w1 12679 163 ∧ 0 ≤ (tableEnvelope C).w2 12679 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12679 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12679 163 ∧ 0 ≤ d.f1 12679 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12679 163 ∧ 0 ≤ d.w1 12679 163 ∧ 0 ≤ d.w2 12679 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12679 ≤ 2 * (228 / 100 : ℝ) / 12679 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12679 ≤ 2 * (370 / 100 : ℝ) / 12679 := by
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
    (completeRAData (tableEnvelope C) 12679 163).locationBound 12679 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12679 163).energyBound 12679 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12679 163) (d.f1 12679 163) d.f2 ≤
      32 * (((4601701893 / 1000000000000000000) : ℝ) + (1535205753 / 1000000000000000000) + (92246823 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12679 163) (d.w1 12679 163)
      (d.w2 12679 163) ≤
      32 * (((1842323581 / 100000000000000000000) : ℝ) + (1310778071 / 100000000000000000000) + (47892541 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12679 163) (d.f1 12679 163) d.f2 ≤
      ((4601701893 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4601701893 / 1000000000000000000)) * ((1535205753 / 1000000000000000000)) * (126 / 100) +
      2 * (((1535205753 / 1000000000000000000)) ^ 2 + 2 * ((4601701893 / 1000000000000000000)) * ((92246823 / 250000000000000000))) +
      6 * ((1535205753 / 1000000000000000000)) * ((92246823 / 250000000000000000)) * (126 / 100) + 8 * ((92246823 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12679 163) (d.f1 12679 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12679 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12679 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12679 163) (d.f1 12679 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12679 163) (d.w1 12679 163) (d.w2 12679 163)
  have hwexpr0 : 0 ≤ d.w0 12679 163 + d.w1 12679 163 * √(π / 2) +
      2 * d.w2 12679 163 + energyR16 12679 *
      radiusPolynomialRoot16 (d.w0 12679 163) (d.w1 12679 163) (d.w2 12679 163) := by
    positivity
  constructor
  · change (12679 : ℝ) ^ 8 * (mA 12679 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12679 163) (d.f1 12679 163) d.f2 + locationR16 12679 *
        radiusPolynomialRoot16 (d.f0 12679 163) (d.f1 12679 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12679 : ℝ) ^ 8 * (mA 12679 : ℝ) ^ 8 *
        ((((4601701893 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4601701893 / 1000000000000000000)) * ((1535205753 / 1000000000000000000)) * (126 / 100) +
          2 * (((1535205753 / 1000000000000000000)) ^ 2 + 2 * ((4601701893 / 1000000000000000000)) * ((92246823 / 250000000000000000))) +
          6 * ((1535205753 / 1000000000000000000)) * ((92246823 / 250000000000000000)) * (126 / 100) + 8 * ((92246823 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12679) *
          (32 * (((4601701893 / 1000000000000000000) : ℝ) + (1535205753 / 1000000000000000000) + (92246823 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12679 : ℝ) ^ 16 *
      (d.w0 12679 163 + d.w1 12679 163 * √(π / 2) + 2 * d.w2 12679 163 +
        energyR16 12679 * radiusPolynomialRoot16 (d.w0 12679 163) (d.w1 12679 163)
          (d.w2 12679 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12679 : ℝ) ^ 16 *
        (((1842323581 / 100000000000000000000) : ℝ) + ((1310778071 / 100000000000000000000)) * (126 / 100) + 2 * ((47892541 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12679) *
          (32 * (((1842323581 / 100000000000000000000) : ℝ) + (1310778071 / 100000000000000000000) + (47892541 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12679

/-! A coarse bound on the actual paper statistics constant at dimension 12680. -/
namespace BstLean.Part266.Row12680
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12678 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12678 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12678 128 ≤ (12932 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12932 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12680) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12680 : ℕ))
    (by norm_num : (12680 : ℕ) ≤ 16384)
  have ht : paperTail256 12680 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12680 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12680 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12680 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12680 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12680 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12678 128 * √(2 / (12680 : ℝ)) *
      (√(12680 : ℝ) + paperT0 12680 + paperTail256 12680) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12680 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12680 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12680 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12678 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12678 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12680 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12680

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12680
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12680 (61 / 100) 163 (17 / (100 * 12680)) (26 / (10 * 12680)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12680 (61 / 100) 163 (17 / (100 * 12680)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (11970177 / 2500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1510432451 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1036605463 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12680 / 12680 * (61 / 100)) ^ 4 * inverseRadius8 (12680 - 1) /
            envelopeGap 12680 (61 / 100) 163 (17 / (100 * 12680)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12680

namespace BstLean.Part266.Row12680
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12680 163 ≤ (4600796821 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12680 163 ≤ (76745179 / 50000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (92228651 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12680 163 ≤ (460472041 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12680 163 ≤ (81904261 / 6250000000000000000)
  w2 : (tableEnvelope C).w2 12680 163 ≤ (478812101 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (11970177 / 2500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (11970177 / 2500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1510432451 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1036605463 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((915387 / 250000000) : ℝ) ≤ √(17 / (100 * 12680) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12680) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1094083041 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38864282459 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12680) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12680) ≤ (111531039 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12680) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12680 * (163 : ℝ) ^ 2 + 26 / (10 * 12680) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12680) : ℝ)) (tA 12680 * 163 ^ 2 + 26 / (10 * 12680)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((915387 / 250000000))) * ((11970177 / 2500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((915387 / 250000000)) ^ 3) * ((1510432451 / 1000000000000000000000000))) + ((1036605463 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((915387 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12680) : ℝ)) d.D d.V d.P (√(tA 12680) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((915387 / 250000000)) ^ 2 * (((1094083041 / 500000000000000)) * ((38864282459 / 1000000000000000000)))) + ((1036605463 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12680) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((915387 / 250000000)) * ((11970177 / 2500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12680) : ℝ)) (tA 12680 * 163 ^ 2 + 26 / (10 * 12680)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((11970177 / 2500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((915387 / 250000000)) ^ 2) * ((1510432451 / 1000000000000000000000000)) + ((1036605463 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12680) : ℝ)) (√(26 / (10 * 12680) : ℝ)) d.D d.V d.P (√(tA 12680) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((915387 / 250000000)) * (((1094083041 / 500000000000000)) * ((38864282459 / 1000000000000000000))) + ((1036605463 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12680) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((11970177 / 2500000000000000000) : ℝ) + ((1036605463 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12680

namespace BstLean.Part266.Row12680
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12680 163 ∧
    0 ≤ (tableEnvelope C).f1 12680 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12680 163 ∧
    0 ≤ (tableEnvelope C).w1 12680 163 ∧ 0 ≤ (tableEnvelope C).w2 12680 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12680 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12680 163 ∧ 0 ≤ d.f1 12680 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12680 163 ∧ 0 ≤ d.w1 12680 163 ∧ 0 ≤ d.w2 12680 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12680 ≤ 2 * (228 / 100 : ℝ) / 12680 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12680 ≤ 2 * (370 / 100 : ℝ) / 12680 := by
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
    (completeRAData (tableEnvelope C) 12680 163).locationBound 12680 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12680 163).energyBound 12680 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12680 163) (d.f1 12680 163) d.f2 ≤
      32 * (((4600796821 / 1000000000000000000) : ℝ) + (76745179 / 50000000000000000) + (92228651 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12680 163) (d.w1 12680 163)
      (d.w2 12680 163) ≤
      32 * (((460472041 / 25000000000000000000) : ℝ) + (81904261 / 6250000000000000000) + (478812101 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12680 163) (d.f1 12680 163) d.f2 ≤
      ((4600796821 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4600796821 / 1000000000000000000)) * ((76745179 / 50000000000000000)) * (126 / 100) +
      2 * (((76745179 / 50000000000000000)) ^ 2 + 2 * ((4600796821 / 1000000000000000000)) * ((92228651 / 250000000000000000))) +
      6 * ((76745179 / 50000000000000000)) * ((92228651 / 250000000000000000)) * (126 / 100) + 8 * ((92228651 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12680 163) (d.f1 12680 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12680 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12680 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12680 163) (d.f1 12680 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12680 163) (d.w1 12680 163) (d.w2 12680 163)
  have hwexpr0 : 0 ≤ d.w0 12680 163 + d.w1 12680 163 * √(π / 2) +
      2 * d.w2 12680 163 + energyR16 12680 *
      radiusPolynomialRoot16 (d.w0 12680 163) (d.w1 12680 163) (d.w2 12680 163) := by
    positivity
  constructor
  · change (12680 : ℝ) ^ 8 * (mA 12680 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12680 163) (d.f1 12680 163) d.f2 + locationR16 12680 *
        radiusPolynomialRoot16 (d.f0 12680 163) (d.f1 12680 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12680 : ℝ) ^ 8 * (mA 12680 : ℝ) ^ 8 *
        ((((4600796821 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4600796821 / 1000000000000000000)) * ((76745179 / 50000000000000000)) * (126 / 100) +
          2 * (((76745179 / 50000000000000000)) ^ 2 + 2 * ((4600796821 / 1000000000000000000)) * ((92228651 / 250000000000000000))) +
          6 * ((76745179 / 50000000000000000)) * ((92228651 / 250000000000000000)) * (126 / 100) + 8 * ((92228651 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12680) *
          (32 * (((4600796821 / 1000000000000000000) : ℝ) + (76745179 / 50000000000000000) + (92228651 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12680 : ℝ) ^ 16 *
      (d.w0 12680 163 + d.w1 12680 163 * √(π / 2) + 2 * d.w2 12680 163 +
        energyR16 12680 * radiusPolynomialRoot16 (d.w0 12680 163) (d.w1 12680 163)
          (d.w2 12680 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12680 : ℝ) ^ 16 *
        (((460472041 / 25000000000000000000) : ℝ) + ((81904261 / 6250000000000000000)) * (126 / 100) + 2 * ((478812101 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12680) *
          (32 * (((460472041 / 25000000000000000000) : ℝ) + (81904261 / 6250000000000000000) + (478812101 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12680

/-! A coarse bound on the actual paper statistics constant at dimension 12681. -/
namespace BstLean.Part266.Row12681
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12679 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12679 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12679 128 ≤ (12933 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12933 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12681) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12681 : ℕ))
    (by norm_num : (12681 : ℕ) ≤ 16384)
  have ht : paperTail256 12681 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12681 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12681 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12681 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12681 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12681 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12679 128 * √(2 / (12681 : ℝ)) *
      (√(12681 : ℝ) + paperT0 12681 + paperTail256 12681) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12681 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12681 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12681 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12679 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12679 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12681 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12681

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12681
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12681 (61 / 100) 163 (17 / (100 * 12681)) (26 / (10 * 12681)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12681 (61 / 100) 163 (17 / (100 * 12681)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (478693809 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1509956049 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2589863249 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12681 / 12681 * (61 / 100)) ^ 4 * inverseRadius8 (12681 - 1) /
            envelopeGap 12681 (61 / 100) 163 (17 / (100 * 12681)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12681

namespace BstLean.Part266.Row12681
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12681 163 ≤ (2299944217 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12681 163 ≤ (306920133 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (92210459 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12681 163 ≤ (230181519 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 12681 163 ≤ (655079013 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12681 163 ≤ (478698827 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (478693809 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (478693809 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1509956049 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2589863249 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((915351 / 250000000) : ℝ) ≤ √(17 / (100 * 12681) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12681) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (54697681 / 25000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38858152929 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12681) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12681) ≤ (111522243 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12681) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12681 * (163 : ℝ) ^ 2 + 26 / (10 * 12681) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12681) : ℝ)) (tA 12681 * 163 ^ 2 + 26 / (10 * 12681)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((915351 / 250000000))) * ((478693809 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((915351 / 250000000)) ^ 3) * ((1509956049 / 1000000000000000000000000))) + ((2589863249 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((915351 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12681) : ℝ)) d.D d.V d.P (√(tA 12681) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((915351 / 250000000)) ^ 2 * (((54697681 / 25000000000000)) * ((38858152929 / 1000000000000000000)))) + ((2589863249 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12681) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((915351 / 250000000)) * ((478693809 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12681) : ℝ)) (tA 12681 * 163 ^ 2 + 26 / (10 * 12681)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((478693809 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((915351 / 250000000)) ^ 2) * ((1509956049 / 1000000000000000000000000)) + ((2589863249 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12681) : ℝ)) (√(26 / (10 * 12681) : ℝ)) d.D d.V d.P (√(tA 12681) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((915351 / 250000000)) * (((54697681 / 25000000000000)) * ((38858152929 / 1000000000000000000))) + ((2589863249 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12681) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((478693809 / 100000000000000000000) : ℝ) + ((2589863249 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12681

namespace BstLean.Part266.Row12681
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12681 163 ∧
    0 ≤ (tableEnvelope C).f1 12681 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12681 163 ∧
    0 ≤ (tableEnvelope C).w1 12681 163 ∧ 0 ≤ (tableEnvelope C).w2 12681 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12681 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12681 163 ∧ 0 ≤ d.f1 12681 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12681 163 ∧ 0 ≤ d.w1 12681 163 ∧ 0 ≤ d.w2 12681 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12681 ≤ 2 * (228 / 100 : ℝ) / 12681 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12681 ≤ 2 * (370 / 100 : ℝ) / 12681 := by
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
    (completeRAData (tableEnvelope C) 12681 163).locationBound 12681 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12681 163).energyBound 12681 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12681 163) (d.f1 12681 163) d.f2 ≤
      32 * (((2299944217 / 500000000000000000) : ℝ) + (306920133 / 200000000000000000) + (92210459 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12681 163) (d.w1 12681 163)
      (d.w2 12681 163) ≤
      32 * (((230181519 / 12500000000000000000) : ℝ) + (655079013 / 50000000000000000000) + (478698827 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12681 163) (d.f1 12681 163) d.f2 ≤
      ((2299944217 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2299944217 / 500000000000000000)) * ((306920133 / 200000000000000000)) * (126 / 100) +
      2 * (((306920133 / 200000000000000000)) ^ 2 + 2 * ((2299944217 / 500000000000000000)) * ((92210459 / 250000000000000000))) +
      6 * ((306920133 / 200000000000000000)) * ((92210459 / 250000000000000000)) * (126 / 100) + 8 * ((92210459 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12681 163) (d.f1 12681 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12681 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12681 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12681 163) (d.f1 12681 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12681 163) (d.w1 12681 163) (d.w2 12681 163)
  have hwexpr0 : 0 ≤ d.w0 12681 163 + d.w1 12681 163 * √(π / 2) +
      2 * d.w2 12681 163 + energyR16 12681 *
      radiusPolynomialRoot16 (d.w0 12681 163) (d.w1 12681 163) (d.w2 12681 163) := by
    positivity
  constructor
  · change (12681 : ℝ) ^ 8 * (mA 12681 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12681 163) (d.f1 12681 163) d.f2 + locationR16 12681 *
        radiusPolynomialRoot16 (d.f0 12681 163) (d.f1 12681 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12681 : ℝ) ^ 8 * (mA 12681 : ℝ) ^ 8 *
        ((((2299944217 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2299944217 / 500000000000000000)) * ((306920133 / 200000000000000000)) * (126 / 100) +
          2 * (((306920133 / 200000000000000000)) ^ 2 + 2 * ((2299944217 / 500000000000000000)) * ((92210459 / 250000000000000000))) +
          6 * ((306920133 / 200000000000000000)) * ((92210459 / 250000000000000000)) * (126 / 100) + 8 * ((92210459 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12681) *
          (32 * (((2299944217 / 500000000000000000) : ℝ) + (306920133 / 200000000000000000) + (92210459 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12681 : ℝ) ^ 16 *
      (d.w0 12681 163 + d.w1 12681 163 * √(π / 2) + 2 * d.w2 12681 163 +
        energyR16 12681 * radiusPolynomialRoot16 (d.w0 12681 163) (d.w1 12681 163)
          (d.w2 12681 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12681 : ℝ) ^ 16 *
        (((230181519 / 12500000000000000000) : ℝ) + ((655079013 / 50000000000000000000)) * (126 / 100) + 2 * ((478698827 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12681) *
          (32 * (((230181519 / 12500000000000000000) : ℝ) + (655079013 / 50000000000000000000) + (478698827 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12681

/-! A coarse bound on the actual paper statistics constant at dimension 12682. -/
namespace BstLean.Part266.Row12682
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12680 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12680 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12680 128 ≤ (12934 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12934 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12682) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12682 : ℕ))
    (by norm_num : (12682 : ℕ) ≤ 16384)
  have ht : paperTail256 12682 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12682 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12682 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12682 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12682 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12682 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12680 128 * √(2 / (12682 : ℝ)) *
      (√(12682 : ℝ) + paperT0 12682 + paperTail256 12682) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12682 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12682 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12682 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12680 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12680 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12682 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12682

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12682
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12682 (61 / 100) 163 (17 / (100 * 12682)) (26 / (10 * 12682)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12682 (61 / 100) 163 (17 / (100 * 12682)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (19143223 / 4000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (301895967 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5176428047 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12682 / 12682 * (61 / 100)) ^ 4 * inverseRadius8 (12682 - 1) /
            envelopeGap 12682 (61 / 100) 163 (17 / (100 * 12682)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12682

namespace BstLean.Part266.Row12682
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12682 163 ≤ (114974509 / 25000000000000000)
  f1 : (tableEnvelope C).f1 12682 163 ≤ (30685957 / 20000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (36876909 / 100000000000000000)
  w0 : (tableEnvelope C).w0 12682 163 ≤ (460254073 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12682 163 ≤ (654923991 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12682 163 ≤ (47858559 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (19143223 / 4000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (19143223 / 4000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (301895967 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5176428047 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((183063 / 50000000) : ℝ) ≤ √(17 / (100 * 12682) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12682) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2187648453 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38852024851 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12682) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12682) ≤ (2230269 / 20000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12682) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12682 * (163 : ℝ) ^ 2 + 26 / (10 * 12682) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12682) : ℝ)) (tA 12682 * 163 ^ 2 + 26 / (10 * 12682)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((183063 / 50000000))) * ((19143223 / 4000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((183063 / 50000000)) ^ 3) * ((301895967 / 200000000000000000000000))) + ((5176428047 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((183063 / 50000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12682) : ℝ)) d.D d.V d.P (√(tA 12682) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((183063 / 50000000)) ^ 2 * (((2187648453 / 1000000000000000)) * ((38852024851 / 1000000000000000000)))) + ((5176428047 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12682) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((183063 / 50000000)) * ((19143223 / 4000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12682) : ℝ)) (tA 12682 * 163 ^ 2 + 26 / (10 * 12682)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((19143223 / 4000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((183063 / 50000000)) ^ 2) * ((301895967 / 200000000000000000000000)) + ((5176428047 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12682) : ℝ)) (√(26 / (10 * 12682) : ℝ)) d.D d.V d.P (√(tA 12682) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((183063 / 50000000)) * (((2187648453 / 1000000000000000)) * ((38852024851 / 1000000000000000000))) + ((5176428047 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12682) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((19143223 / 4000000000000000000) : ℝ) + ((5176428047 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12682

namespace BstLean.Part266.Row12682
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12682 163 ∧
    0 ≤ (tableEnvelope C).f1 12682 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12682 163 ∧
    0 ≤ (tableEnvelope C).w1 12682 163 ∧ 0 ≤ (tableEnvelope C).w2 12682 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12682 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12682 163 ∧ 0 ≤ d.f1 12682 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12682 163 ∧ 0 ≤ d.w1 12682 163 ∧ 0 ≤ d.w2 12682 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12682 ≤ 2 * (228 / 100 : ℝ) / 12682 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12682 ≤ 2 * (370 / 100 : ℝ) / 12682 := by
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
    (completeRAData (tableEnvelope C) 12682 163).locationBound 12682 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12682 163).energyBound 12682 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12682 163) (d.f1 12682 163) d.f2 ≤
      32 * (((114974509 / 25000000000000000) : ℝ) + (30685957 / 20000000000000000) + (36876909 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12682 163) (d.w1 12682 163)
      (d.w2 12682 163) ≤
      32 * (((460254073 / 25000000000000000000) : ℝ) + (654923991 / 50000000000000000000) + (47858559 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12682 163) (d.f1 12682 163) d.f2 ≤
      ((114974509 / 25000000000000000) : ℝ) ^ 2 + 2 * ((114974509 / 25000000000000000)) * ((30685957 / 20000000000000000)) * (126 / 100) +
      2 * (((30685957 / 20000000000000000)) ^ 2 + 2 * ((114974509 / 25000000000000000)) * ((36876909 / 100000000000000000))) +
      6 * ((30685957 / 20000000000000000)) * ((36876909 / 100000000000000000)) * (126 / 100) + 8 * ((36876909 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12682 163) (d.f1 12682 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12682 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12682 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12682 163) (d.f1 12682 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12682 163) (d.w1 12682 163) (d.w2 12682 163)
  have hwexpr0 : 0 ≤ d.w0 12682 163 + d.w1 12682 163 * √(π / 2) +
      2 * d.w2 12682 163 + energyR16 12682 *
      radiusPolynomialRoot16 (d.w0 12682 163) (d.w1 12682 163) (d.w2 12682 163) := by
    positivity
  constructor
  · change (12682 : ℝ) ^ 8 * (mA 12682 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12682 163) (d.f1 12682 163) d.f2 + locationR16 12682 *
        radiusPolynomialRoot16 (d.f0 12682 163) (d.f1 12682 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12682 : ℝ) ^ 8 * (mA 12682 : ℝ) ^ 8 *
        ((((114974509 / 25000000000000000) : ℝ) ^ 2 + 2 * ((114974509 / 25000000000000000)) * ((30685957 / 20000000000000000)) * (126 / 100) +
          2 * (((30685957 / 20000000000000000)) ^ 2 + 2 * ((114974509 / 25000000000000000)) * ((36876909 / 100000000000000000))) +
          6 * ((30685957 / 20000000000000000)) * ((36876909 / 100000000000000000)) * (126 / 100) + 8 * ((36876909 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12682) *
          (32 * (((114974509 / 25000000000000000) : ℝ) + (30685957 / 20000000000000000) + (36876909 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12682 : ℝ) ^ 16 *
      (d.w0 12682 163 + d.w1 12682 163 * √(π / 2) + 2 * d.w2 12682 163 +
        energyR16 12682 * radiusPolynomialRoot16 (d.w0 12682 163) (d.w1 12682 163)
          (d.w2 12682 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12682 : ℝ) ^ 16 *
        (((460254073 / 25000000000000000000) : ℝ) + ((654923991 / 50000000000000000000)) * (126 / 100) + 2 * ((47858559 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12682) *
          (32 * (((460254073 / 25000000000000000000) : ℝ) + (654923991 / 50000000000000000000) + (47858559 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12682

/-! A coarse bound on the actual paper statistics constant at dimension 12683. -/
namespace BstLean.Part266.Row12683
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12681 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12681 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12681 128 ≤ (12935 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12935 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12683) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12683 : ℕ))
    (by norm_num : (12683 : ℕ) ≤ 16384)
  have ht : paperTail256 12683 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12683 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12683 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12683 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12683 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12683 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12681 128 * √(2 / (12683 : ℝ)) *
      (√(12683 : ℝ) + paperT0 12683 + paperTail256 12683) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12683 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12683 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12683 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12681 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12681 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12683 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12683

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12683
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12683 (61 / 100) 163 (17 / (100 * 12683)) (26 / (10 * 12683)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12683 (61 / 100) 163 (17 / (100 * 12683)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (29904211 / 6250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (47156369 / 31250000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2586565981 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12683 / 12683 * (61 / 100)) ^ 4 * inverseRadius8 (12683 - 1) /
            envelopeGap 12683 (61 / 100) 163 (17 / (100 * 12683)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12683

namespace BstLean.Part266.Row12683
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12683 163 ≤ (4598076223 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12683 163 ≤ (1533995969 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (368696467 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12683 163 ≤ (73623253 / 4000000000000000000)
  w1 : (tableEnvelope C).w1 12683 163 ≤ (654769199 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12683 163 ≤ (119618097 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (29904211 / 6250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (29904211 / 6250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (47156369 / 31250000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2586565981 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((732223 / 200000000) : ℝ) ≤ √(17 / (100 * 12683) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12683) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1093694857 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19422949107 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12683) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12683) ≤ (111504657 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12683) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12683 * (163 : ℝ) ^ 2 + 26 / (10 * 12683) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12683) : ℝ)) (tA 12683 * 163 ^ 2 + 26 / (10 * 12683)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((732223 / 200000000))) * ((29904211 / 6250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((732223 / 200000000)) ^ 3) * ((47156369 / 31250000000000000000000))) + ((2586565981 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((732223 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12683) : ℝ)) d.D d.V d.P (√(tA 12683) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((732223 / 200000000)) ^ 2 * (((1093694857 / 500000000000000)) * ((19422949107 / 500000000000000000)))) + ((2586565981 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12683) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((732223 / 200000000)) * ((29904211 / 6250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12683) : ℝ)) (tA 12683 * 163 ^ 2 + 26 / (10 * 12683)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((29904211 / 6250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((732223 / 200000000)) ^ 2) * ((47156369 / 31250000000000000000000)) + ((2586565981 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12683) : ℝ)) (√(26 / (10 * 12683) : ℝ)) d.D d.V d.P (√(tA 12683) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((732223 / 200000000)) * (((1093694857 / 500000000000000)) * ((19422949107 / 500000000000000000))) + ((2586565981 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12683) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((29904211 / 6250000000000000000) : ℝ) + ((2586565981 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12683

namespace BstLean.Part266.Row12683
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12683 163 ∧
    0 ≤ (tableEnvelope C).f1 12683 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12683 163 ∧
    0 ≤ (tableEnvelope C).w1 12683 163 ∧ 0 ≤ (tableEnvelope C).w2 12683 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12683 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12683 163 ∧ 0 ≤ d.f1 12683 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12683 163 ∧ 0 ≤ d.w1 12683 163 ∧ 0 ≤ d.w2 12683 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12683 ≤ 2 * (228 / 100 : ℝ) / 12683 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12683 ≤ 2 * (370 / 100 : ℝ) / 12683 := by
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
    (completeRAData (tableEnvelope C) 12683 163).locationBound 12683 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12683 163).energyBound 12683 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12683 163) (d.f1 12683 163) d.f2 ≤
      32 * (((4598076223 / 1000000000000000000) : ℝ) + (1533995969 / 1000000000000000000) + (368696467 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12683 163) (d.w1 12683 163)
      (d.w2 12683 163) ≤
      32 * (((73623253 / 4000000000000000000) : ℝ) + (654769199 / 50000000000000000000) + (119618097 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12683 163) (d.f1 12683 163) d.f2 ≤
      ((4598076223 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4598076223 / 1000000000000000000)) * ((1533995969 / 1000000000000000000)) * (126 / 100) +
      2 * (((1533995969 / 1000000000000000000)) ^ 2 + 2 * ((4598076223 / 1000000000000000000)) * ((368696467 / 1000000000000000000))) +
      6 * ((1533995969 / 1000000000000000000)) * ((368696467 / 1000000000000000000)) * (126 / 100) + 8 * ((368696467 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12683 163) (d.f1 12683 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12683 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12683 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12683 163) (d.f1 12683 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12683 163) (d.w1 12683 163) (d.w2 12683 163)
  have hwexpr0 : 0 ≤ d.w0 12683 163 + d.w1 12683 163 * √(π / 2) +
      2 * d.w2 12683 163 + energyR16 12683 *
      radiusPolynomialRoot16 (d.w0 12683 163) (d.w1 12683 163) (d.w2 12683 163) := by
    positivity
  constructor
  · change (12683 : ℝ) ^ 8 * (mA 12683 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12683 163) (d.f1 12683 163) d.f2 + locationR16 12683 *
        radiusPolynomialRoot16 (d.f0 12683 163) (d.f1 12683 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12683 : ℝ) ^ 8 * (mA 12683 : ℝ) ^ 8 *
        ((((4598076223 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4598076223 / 1000000000000000000)) * ((1533995969 / 1000000000000000000)) * (126 / 100) +
          2 * (((1533995969 / 1000000000000000000)) ^ 2 + 2 * ((4598076223 / 1000000000000000000)) * ((368696467 / 1000000000000000000))) +
          6 * ((1533995969 / 1000000000000000000)) * ((368696467 / 1000000000000000000)) * (126 / 100) + 8 * ((368696467 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12683) *
          (32 * (((4598076223 / 1000000000000000000) : ℝ) + (1533995969 / 1000000000000000000) + (368696467 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12683 : ℝ) ^ 16 *
      (d.w0 12683 163 + d.w1 12683 163 * √(π / 2) + 2 * d.w2 12683 163 +
        energyR16 12683 * radiusPolynomialRoot16 (d.w0 12683 163) (d.w1 12683 163)
          (d.w2 12683 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12683 : ℝ) ^ 16 *
        (((73623253 / 4000000000000000000) : ℝ) + ((654769199 / 50000000000000000000)) * (126 / 100) + 2 * ((119618097 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12683) *
          (32 * (((73623253 / 4000000000000000000) : ℝ) + (654769199 / 50000000000000000000) + (119618097 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12683

/-! A coarse bound on the actual paper statistics constant at dimension 12684. -/
namespace BstLean.Part266.Row12684
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12682 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12682 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12682 128 ≤ (12936 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12936 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12684) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12684 : ℕ))
    (by norm_num : (12684 : ℕ) ≤ 16384)
  have ht : paperTail256 12684 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12684 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12684 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12684 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12684 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12684 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12682 128 * √(2 / (12684 : ℝ)) *
      (√(12684 : ℝ) + paperT0 12684 + paperTail256 12684) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12684 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12684 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12684 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12682 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12682 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12684 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12684

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12684
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12684 (61 / 100) 163 (17 / (100 * 12684)) (26 / (10 * 12684)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12684 (61 / 100) 163 (17 / (100 * 12684)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (119588553 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (150852797 / 100000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5169838241 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12684 / 12684 * (61 / 100)) ^ 4 * inverseRadius8 (12684 - 1) /
            envelopeGap 12684 (61 / 100) 163 (17 / (100 * 12684)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12684

namespace BstLean.Part266.Row12684
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12684 163 ≤ (183886751 / 40000000000000000)
  f1 : (tableEnvelope C).f1 12684 163 ≤ (383423337 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (92155941 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12684 163 ≤ (460036441 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12684 163 ≤ (1309228559 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12684 163 ≤ (23917961 / 5000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (119588553 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (119588553 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (150852797 / 100000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5169838241 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3660971 / 1000000000) : ℝ) ≤ √(17 / (100 * 12684) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12684) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (87485241 / 40000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38839773043 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12684) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12684) ≤ (55747933 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12684) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12684 * (163 : ℝ) ^ 2 + 26 / (10 * 12684) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12684) : ℝ)) (tA 12684 * 163 ^ 2 + 26 / (10 * 12684)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3660971 / 1000000000))) * ((119588553 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3660971 / 1000000000)) ^ 3) * ((150852797 / 100000000000000000000000))) + ((5169838241 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3660971 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12684) : ℝ)) d.D d.V d.P (√(tA 12684) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3660971 / 1000000000)) ^ 2 * (((87485241 / 40000000000000)) * ((38839773043 / 1000000000000000000)))) + ((5169838241 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12684) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3660971 / 1000000000)) * ((119588553 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12684) : ℝ)) (tA 12684 * 163 ^ 2 + 26 / (10 * 12684)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((119588553 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3660971 / 1000000000)) ^ 2) * ((150852797 / 100000000000000000000000)) + ((5169838241 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12684) : ℝ)) (√(26 / (10 * 12684) : ℝ)) d.D d.V d.P (√(tA 12684) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3660971 / 1000000000)) * (((87485241 / 40000000000000)) * ((38839773043 / 1000000000000000000))) + ((5169838241 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12684) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((119588553 / 25000000000000000000) : ℝ) + ((5169838241 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12684

namespace BstLean.Part266.Row12684
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12684 163 ∧
    0 ≤ (tableEnvelope C).f1 12684 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12684 163 ∧
    0 ≤ (tableEnvelope C).w1 12684 163 ∧ 0 ≤ (tableEnvelope C).w2 12684 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12684 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12684 163 ∧ 0 ≤ d.f1 12684 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12684 163 ∧ 0 ≤ d.w1 12684 163 ∧ 0 ≤ d.w2 12684 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12684 ≤ 2 * (228 / 100 : ℝ) / 12684 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12684 ≤ 2 * (370 / 100 : ℝ) / 12684 := by
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
    (completeRAData (tableEnvelope C) 12684 163).locationBound 12684 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12684 163).energyBound 12684 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12684 163) (d.f1 12684 163) d.f2 ≤
      32 * (((183886751 / 40000000000000000) : ℝ) + (383423337 / 250000000000000000) + (92155941 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12684 163) (d.w1 12684 163)
      (d.w2 12684 163) ≤
      32 * (((460036441 / 25000000000000000000) : ℝ) + (1309228559 / 100000000000000000000) + (23917961 / 5000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12684 163) (d.f1 12684 163) d.f2 ≤
      ((183886751 / 40000000000000000) : ℝ) ^ 2 + 2 * ((183886751 / 40000000000000000)) * ((383423337 / 250000000000000000)) * (126 / 100) +
      2 * (((383423337 / 250000000000000000)) ^ 2 + 2 * ((183886751 / 40000000000000000)) * ((92155941 / 250000000000000000))) +
      6 * ((383423337 / 250000000000000000)) * ((92155941 / 250000000000000000)) * (126 / 100) + 8 * ((92155941 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12684 163) (d.f1 12684 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12684 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12684 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12684 163) (d.f1 12684 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12684 163) (d.w1 12684 163) (d.w2 12684 163)
  have hwexpr0 : 0 ≤ d.w0 12684 163 + d.w1 12684 163 * √(π / 2) +
      2 * d.w2 12684 163 + energyR16 12684 *
      radiusPolynomialRoot16 (d.w0 12684 163) (d.w1 12684 163) (d.w2 12684 163) := by
    positivity
  constructor
  · change (12684 : ℝ) ^ 8 * (mA 12684 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12684 163) (d.f1 12684 163) d.f2 + locationR16 12684 *
        radiusPolynomialRoot16 (d.f0 12684 163) (d.f1 12684 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12684 : ℝ) ^ 8 * (mA 12684 : ℝ) ^ 8 *
        ((((183886751 / 40000000000000000) : ℝ) ^ 2 + 2 * ((183886751 / 40000000000000000)) * ((383423337 / 250000000000000000)) * (126 / 100) +
          2 * (((383423337 / 250000000000000000)) ^ 2 + 2 * ((183886751 / 40000000000000000)) * ((92155941 / 250000000000000000))) +
          6 * ((383423337 / 250000000000000000)) * ((92155941 / 250000000000000000)) * (126 / 100) + 8 * ((92155941 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12684) *
          (32 * (((183886751 / 40000000000000000) : ℝ) + (383423337 / 250000000000000000) + (92155941 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12684 : ℝ) ^ 16 *
      (d.w0 12684 163 + d.w1 12684 163 * √(π / 2) + 2 * d.w2 12684 163 +
        energyR16 12684 * radiusPolynomialRoot16 (d.w0 12684 163) (d.w1 12684 163)
          (d.w2 12684 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12684 : ℝ) ^ 16 *
        (((460036441 / 25000000000000000000) : ℝ) + ((1309228559 / 100000000000000000000)) * (126 / 100) + 2 * ((23917961 / 5000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12684) *
          (32 * (((460036441 / 25000000000000000000) : ℝ) + (1309228559 / 100000000000000000000) + (23917961 / 5000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12684

/-! A coarse bound on the actual paper statistics constant at dimension 12685. -/
namespace BstLean.Part266.Row12685
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12683 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12683 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12683 128 ≤ (12937 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12937 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12685) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12685 : ℕ))
    (by norm_num : (12685 : ℕ) ≤ 16384)
  have ht : paperTail256 12685 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12685 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12685 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12685 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12685 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12685 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12683 128 * √(2 / (12685 : ℝ)) *
      (√(12685 : ℝ) + paperT0 12685 + paperTail256 12685) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12685 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12685 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12685 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12683 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12683 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12685 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12685

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12685
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12685 (61 / 100) 163 (17 / (100 * 12685)) (26 / (10 * 12685)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12685 (61 / 100) 163 (17 / (100 * 12685)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (95648217 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (754026159 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5166546881 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12685 / 12685 * (61 / 100)) ^ 4 * inverseRadius8 (12685 - 1) /
            envelopeGap 12685 (61 / 100) 163 (17 / (100 * 12685)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12685

namespace BstLean.Part266.Row12685
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12685 163 ≤ (1149065409 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12685 163 ≤ (766695413 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (92137771 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12685 163 ≤ (919855177 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12685 163 ≤ (654459413 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12685 163 ≤ (47824609 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (95648217 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (95648217 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (754026159 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5166546881 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3660827 / 1000000000) : ℝ) ≤ √(17 / (100 * 12685) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12685) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (218687239 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38833649301 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12685) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12685) ≤ (111487077 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12685) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12685 * (163 : ℝ) ^ 2 + 26 / (10 * 12685) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12685) : ℝ)) (tA 12685 * 163 ^ 2 + 26 / (10 * 12685)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3660827 / 1000000000))) * ((95648217 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3660827 / 1000000000)) ^ 3) * ((754026159 / 500000000000000000000000))) + ((5166546881 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3660827 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12685) : ℝ)) d.D d.V d.P (√(tA 12685) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3660827 / 1000000000)) ^ 2 * (((218687239 / 100000000000000)) * ((38833649301 / 1000000000000000000)))) + ((5166546881 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12685) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3660827 / 1000000000)) * ((95648217 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12685) : ℝ)) (tA 12685 * 163 ^ 2 + 26 / (10 * 12685)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((95648217 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3660827 / 1000000000)) ^ 2) * ((754026159 / 500000000000000000000000)) + ((5166546881 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12685) : ℝ)) (√(26 / (10 * 12685) : ℝ)) d.D d.V d.P (√(tA 12685) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3660827 / 1000000000)) * (((218687239 / 100000000000000)) * ((38833649301 / 1000000000000000000))) + ((5166546881 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12685) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((95648217 / 20000000000000000000) : ℝ) + ((5166546881 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12685

namespace BstLean.Part266.Row12685
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12685 163 ∧
    0 ≤ (tableEnvelope C).f1 12685 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12685 163 ∧
    0 ≤ (tableEnvelope C).w1 12685 163 ∧ 0 ≤ (tableEnvelope C).w2 12685 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12685 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12685 163 ∧ 0 ≤ d.f1 12685 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12685 163 ∧ 0 ≤ d.w1 12685 163 ∧ 0 ≤ d.w2 12685 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12685 ≤ 2 * (228 / 100 : ℝ) / 12685 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12685 ≤ 2 * (370 / 100 : ℝ) / 12685 := by
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
    (completeRAData (tableEnvelope C) 12685 163).locationBound 12685 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12685 163).energyBound 12685 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12685 163) (d.f1 12685 163) d.f2 ≤
      32 * (((1149065409 / 250000000000000000) : ℝ) + (766695413 / 500000000000000000) + (92137771 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12685 163) (d.w1 12685 163)
      (d.w2 12685 163) ≤
      32 * (((919855177 / 50000000000000000000) : ℝ) + (654459413 / 50000000000000000000) + (47824609 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12685 163) (d.f1 12685 163) d.f2 ≤
      ((1149065409 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1149065409 / 250000000000000000)) * ((766695413 / 500000000000000000)) * (126 / 100) +
      2 * (((766695413 / 500000000000000000)) ^ 2 + 2 * ((1149065409 / 250000000000000000)) * ((92137771 / 250000000000000000))) +
      6 * ((766695413 / 500000000000000000)) * ((92137771 / 250000000000000000)) * (126 / 100) + 8 * ((92137771 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12685 163) (d.f1 12685 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12685 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12685 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12685 163) (d.f1 12685 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12685 163) (d.w1 12685 163) (d.w2 12685 163)
  have hwexpr0 : 0 ≤ d.w0 12685 163 + d.w1 12685 163 * √(π / 2) +
      2 * d.w2 12685 163 + energyR16 12685 *
      radiusPolynomialRoot16 (d.w0 12685 163) (d.w1 12685 163) (d.w2 12685 163) := by
    positivity
  constructor
  · change (12685 : ℝ) ^ 8 * (mA 12685 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12685 163) (d.f1 12685 163) d.f2 + locationR16 12685 *
        radiusPolynomialRoot16 (d.f0 12685 163) (d.f1 12685 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12685 : ℝ) ^ 8 * (mA 12685 : ℝ) ^ 8 *
        ((((1149065409 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1149065409 / 250000000000000000)) * ((766695413 / 500000000000000000)) * (126 / 100) +
          2 * (((766695413 / 500000000000000000)) ^ 2 + 2 * ((1149065409 / 250000000000000000)) * ((92137771 / 250000000000000000))) +
          6 * ((766695413 / 500000000000000000)) * ((92137771 / 250000000000000000)) * (126 / 100) + 8 * ((92137771 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12685) *
          (32 * (((1149065409 / 250000000000000000) : ℝ) + (766695413 / 500000000000000000) + (92137771 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12685 : ℝ) ^ 16 *
      (d.w0 12685 163 + d.w1 12685 163 * √(π / 2) + 2 * d.w2 12685 163 +
        energyR16 12685 * radiusPolynomialRoot16 (d.w0 12685 163) (d.w1 12685 163)
          (d.w2 12685 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12685 : ℝ) ^ 16 *
        (((919855177 / 50000000000000000000) : ℝ) + ((654459413 / 50000000000000000000)) * (126 / 100) + 2 * ((47824609 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12685) *
          (32 * (((919855177 / 50000000000000000000) : ℝ) + (654459413 / 50000000000000000000) + (47824609 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12685

/-! A coarse bound on the actual paper statistics constant at dimension 12686. -/
namespace BstLean.Part266.Row12686
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12684 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12684 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12684 128 ≤ (12938 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12938 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12686) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12686 : ℕ))
    (by norm_num : (12686 : ℕ) ≤ 16384)
  have ht : paperTail256 12686 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12686 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12686 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12686 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12686 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12686 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12684 128 * √(2 / (12686 : ℝ)) *
      (√(12686 : ℝ) + paperT0 12686 + paperTail256 12686) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12686 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12686 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12686 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12684 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12684 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12686 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12686

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12686
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12686 (61 / 100) 163 (17 / (100 * 12686)) (26 / (10 * 12686)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12686 (61 / 100) 163 (17 / (100 * 12686)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (59765999 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (753788427 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (129081447 / 25000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12686 / 12686 * (61 / 100)) ^ 4 * inverseRadius8 (12686 - 1) /
            envelopeGap 12686 (61 / 100) 163 (17 / (100 * 12686)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12686

namespace BstLean.Part266.Row12686
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12686 163 ≤ (4595358433 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12686 163 ≤ (1533089237 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (14739141 / 40000000000000000)
  w0 : (tableEnvelope C).w0 12686 163 ≤ (367855167 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12686 163 ≤ (1308609553 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12686 163 ≤ (239066497 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (59765999 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (59765999 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (753788427 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (129081447 / 25000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1830341 / 500000000) : ℝ) ≤ √(17 / (100 * 12686) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12686) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2186613803 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19413763507 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12686) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12686) ≤ (111478289 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12686) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12686 * (163 : ℝ) ^ 2 + 26 / (10 * 12686) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12686) : ℝ)) (tA 12686 * 163 ^ 2 + 26 / (10 * 12686)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1830341 / 500000000))) * ((59765999 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1830341 / 500000000)) ^ 3) * ((753788427 / 500000000000000000000000))) + ((129081447 / 25000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1830341 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12686) : ℝ)) d.D d.V d.P (√(tA 12686) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1830341 / 500000000)) ^ 2 * (((2186613803 / 1000000000000000)) * ((19413763507 / 500000000000000000)))) + ((129081447 / 25000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12686) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1830341 / 500000000)) * ((59765999 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12686) : ℝ)) (tA 12686 * 163 ^ 2 + 26 / (10 * 12686)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((59765999 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1830341 / 500000000)) ^ 2) * ((753788427 / 500000000000000000000000)) + ((129081447 / 25000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12686) : ℝ)) (√(26 / (10 * 12686) : ℝ)) d.D d.V d.P (√(tA 12686) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1830341 / 500000000)) * (((2186613803 / 1000000000000000)) * ((19413763507 / 500000000000000000))) + ((129081447 / 25000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12686) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((59765999 / 12500000000000000000) : ℝ) + ((129081447 / 25000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12686

namespace BstLean.Part266.Row12686
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12686 163 ∧
    0 ≤ (tableEnvelope C).f1 12686 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12686 163 ∧
    0 ≤ (tableEnvelope C).w1 12686 163 ∧ 0 ≤ (tableEnvelope C).w2 12686 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12686 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12686 163 ∧ 0 ≤ d.f1 12686 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12686 163 ∧ 0 ≤ d.w1 12686 163 ∧ 0 ≤ d.w2 12686 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12686 ≤ 2 * (228 / 100 : ℝ) / 12686 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12686 ≤ 2 * (370 / 100 : ℝ) / 12686 := by
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
    (completeRAData (tableEnvelope C) 12686 163).locationBound 12686 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12686 163).energyBound 12686 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12686 163) (d.f1 12686 163) d.f2 ≤
      32 * (((4595358433 / 1000000000000000000) : ℝ) + (1533089237 / 1000000000000000000) + (14739141 / 40000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12686 163) (d.w1 12686 163)
      (d.w2 12686 163) ≤
      32 * (((367855167 / 20000000000000000000) : ℝ) + (1308609553 / 100000000000000000000) + (239066497 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12686 163) (d.f1 12686 163) d.f2 ≤
      ((4595358433 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4595358433 / 1000000000000000000)) * ((1533089237 / 1000000000000000000)) * (126 / 100) +
      2 * (((1533089237 / 1000000000000000000)) ^ 2 + 2 * ((4595358433 / 1000000000000000000)) * ((14739141 / 40000000000000000))) +
      6 * ((1533089237 / 1000000000000000000)) * ((14739141 / 40000000000000000)) * (126 / 100) + 8 * ((14739141 / 40000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12686 163) (d.f1 12686 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12686 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12686 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12686 163) (d.f1 12686 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12686 163) (d.w1 12686 163) (d.w2 12686 163)
  have hwexpr0 : 0 ≤ d.w0 12686 163 + d.w1 12686 163 * √(π / 2) +
      2 * d.w2 12686 163 + energyR16 12686 *
      radiusPolynomialRoot16 (d.w0 12686 163) (d.w1 12686 163) (d.w2 12686 163) := by
    positivity
  constructor
  · change (12686 : ℝ) ^ 8 * (mA 12686 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12686 163) (d.f1 12686 163) d.f2 + locationR16 12686 *
        radiusPolynomialRoot16 (d.f0 12686 163) (d.f1 12686 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12686 : ℝ) ^ 8 * (mA 12686 : ℝ) ^ 8 *
        ((((4595358433 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4595358433 / 1000000000000000000)) * ((1533089237 / 1000000000000000000)) * (126 / 100) +
          2 * (((1533089237 / 1000000000000000000)) ^ 2 + 2 * ((4595358433 / 1000000000000000000)) * ((14739141 / 40000000000000000))) +
          6 * ((1533089237 / 1000000000000000000)) * ((14739141 / 40000000000000000)) * (126 / 100) + 8 * ((14739141 / 40000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12686) *
          (32 * (((4595358433 / 1000000000000000000) : ℝ) + (1533089237 / 1000000000000000000) + (14739141 / 40000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12686 : ℝ) ^ 16 *
      (d.w0 12686 163 + d.w1 12686 163 * √(π / 2) + 2 * d.w2 12686 163 +
        energyR16 12686 * radiusPolynomialRoot16 (d.w0 12686 163) (d.w1 12686 163)
          (d.w2 12686 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12686 : ℝ) ^ 16 *
        (((367855167 / 20000000000000000000) : ℝ) + ((1308609553 / 100000000000000000000)) * (126 / 100) + 2 * ((239066497 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12686) *
          (32 * (((367855167 / 20000000000000000000) : ℝ) + (1308609553 / 100000000000000000000) + (239066497 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12686

/-! A coarse bound on the actual paper statistics constant at dimension 12687. -/
namespace BstLean.Part266.Row12687
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12685 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12685 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12685 128 ≤ (12939 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12939 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12687) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12687 : ℕ))
    (by norm_num : (12687 : ℕ) ≤ 16384)
  have ht : paperTail256 12687 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12687 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12687 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12687 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12687 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12687 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12685 128 * √(2 / (12687 : ℝ)) *
      (√(12687 : ℝ) + paperT0 12687 + paperTail256 12687) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12687 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12687 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12687 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12685 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12685 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12687 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12687

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12687
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12687 (61 / 100) 163 (17 / (100 * 12687)) (26 / (10 * 12687)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12687 (61 / 100) 163 (17 / (100 * 12687)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (59751867 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (753550789 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5159971237 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12687 / 12687 * (61 / 100)) ^ 4 * inverseRadius8 (12687 - 1) /
            envelopeGap 12687 (61 / 100) 163 (17 / (100 * 12687)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12687

namespace BstLean.Part266.Row12687
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12687 163 ≤ (4594451921 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12687 163 ≤ (153278691 / 100000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (2878171 / 7812500000000000)
  w0 : (tableEnvelope C).w0 12687 163 ≤ (73553629 / 4000000000000000000)
  w1 : (tableEnvelope C).w1 12687 163 ≤ (1308300027 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12687 163 ≤ (95603987 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (59751867 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (59751867 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (753550789 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5159971237 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1830269 / 500000000) : ℝ) ≤ √(17 / (100 * 12687) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12687) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2186355269 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38821406183 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12687) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12687) ≤ (55734751 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12687) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12687 * (163 : ℝ) ^ 2 + 26 / (10 * 12687) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12687) : ℝ)) (tA 12687 * 163 ^ 2 + 26 / (10 * 12687)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1830269 / 500000000))) * ((59751867 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1830269 / 500000000)) ^ 3) * ((753550789 / 500000000000000000000000))) + ((5159971237 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1830269 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12687) : ℝ)) d.D d.V d.P (√(tA 12687) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1830269 / 500000000)) ^ 2 * (((2186355269 / 1000000000000000)) * ((38821406183 / 1000000000000000000)))) + ((5159971237 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12687) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1830269 / 500000000)) * ((59751867 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12687) : ℝ)) (tA 12687 * 163 ^ 2 + 26 / (10 * 12687)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((59751867 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1830269 / 500000000)) ^ 2) * ((753550789 / 500000000000000000000000)) + ((5159971237 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12687) : ℝ)) (√(26 / (10 * 12687) : ℝ)) d.D d.V d.P (√(tA 12687) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1830269 / 500000000)) * (((2186355269 / 1000000000000000)) * ((38821406183 / 1000000000000000000))) + ((5159971237 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12687) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((59751867 / 12500000000000000000) : ℝ) + ((5159971237 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12687

namespace BstLean.Part266.Row12687
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12687 163 ∧
    0 ≤ (tableEnvelope C).f1 12687 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12687 163 ∧
    0 ≤ (tableEnvelope C).w1 12687 163 ∧ 0 ≤ (tableEnvelope C).w2 12687 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12687 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12687 163 ∧ 0 ≤ d.f1 12687 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12687 163 ∧ 0 ≤ d.w1 12687 163 ∧ 0 ≤ d.w2 12687 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12687 ≤ 2 * (228 / 100 : ℝ) / 12687 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12687 ≤ 2 * (370 / 100 : ℝ) / 12687 := by
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
    (completeRAData (tableEnvelope C) 12687 163).locationBound 12687 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12687 163).energyBound 12687 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12687 163) (d.f1 12687 163) d.f2 ≤
      32 * (((4594451921 / 1000000000000000000) : ℝ) + (153278691 / 100000000000000000) + (2878171 / 7812500000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12687 163) (d.w1 12687 163)
      (d.w2 12687 163) ≤
      32 * (((73553629 / 4000000000000000000) : ℝ) + (1308300027 / 100000000000000000000) + (95603987 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12687 163) (d.f1 12687 163) d.f2 ≤
      ((4594451921 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4594451921 / 1000000000000000000)) * ((153278691 / 100000000000000000)) * (126 / 100) +
      2 * (((153278691 / 100000000000000000)) ^ 2 + 2 * ((4594451921 / 1000000000000000000)) * ((2878171 / 7812500000000000))) +
      6 * ((153278691 / 100000000000000000)) * ((2878171 / 7812500000000000)) * (126 / 100) + 8 * ((2878171 / 7812500000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12687 163) (d.f1 12687 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12687 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12687 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12687 163) (d.f1 12687 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12687 163) (d.w1 12687 163) (d.w2 12687 163)
  have hwexpr0 : 0 ≤ d.w0 12687 163 + d.w1 12687 163 * √(π / 2) +
      2 * d.w2 12687 163 + energyR16 12687 *
      radiusPolynomialRoot16 (d.w0 12687 163) (d.w1 12687 163) (d.w2 12687 163) := by
    positivity
  constructor
  · change (12687 : ℝ) ^ 8 * (mA 12687 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12687 163) (d.f1 12687 163) d.f2 + locationR16 12687 *
        radiusPolynomialRoot16 (d.f0 12687 163) (d.f1 12687 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12687 : ℝ) ^ 8 * (mA 12687 : ℝ) ^ 8 *
        ((((4594451921 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4594451921 / 1000000000000000000)) * ((153278691 / 100000000000000000)) * (126 / 100) +
          2 * (((153278691 / 100000000000000000)) ^ 2 + 2 * ((4594451921 / 1000000000000000000)) * ((2878171 / 7812500000000000))) +
          6 * ((153278691 / 100000000000000000)) * ((2878171 / 7812500000000000)) * (126 / 100) + 8 * ((2878171 / 7812500000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12687) *
          (32 * (((4594451921 / 1000000000000000000) : ℝ) + (153278691 / 100000000000000000) + (2878171 / 7812500000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12687 : ℝ) ^ 16 *
      (d.w0 12687 163 + d.w1 12687 163 * √(π / 2) + 2 * d.w2 12687 163 +
        energyR16 12687 * radiusPolynomialRoot16 (d.w0 12687 163) (d.w1 12687 163)
          (d.w2 12687 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12687 : ℝ) ^ 16 *
        (((73553629 / 4000000000000000000) : ℝ) + ((1308300027 / 100000000000000000000)) * (126 / 100) + 2 * ((95603987 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12687) *
          (32 * (((73553629 / 4000000000000000000) : ℝ) + (1308300027 / 100000000000000000000) + (95603987 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12687

/-! A coarse bound on the actual paper statistics constant at dimension 12688. -/
namespace BstLean.Part266.Row12688
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12686 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12686 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12686 128 ≤ (12940 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12940 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12688) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12688 : ℕ))
    (by norm_num : (12688 : ℕ) ≤ 16384)
  have ht : paperTail256 12688 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12688 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12688 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12688 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12688 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12688 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12686 128 * √(2 / (12688 : ℝ)) *
      (√(12688 : ℝ) + paperT0 12688 + paperTail256 12688) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12688 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12688 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12688 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12686 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12686 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12688 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12688

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12688
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12688 (61 / 100) 163 (17 / (100 * 12688)) (26 / (10 * 12688)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12688 (61 / 100) 163 (17 / (100 * 12688)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (95580383 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1506626489 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (103133739 / 20000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12688 / 12688 * (61 / 100)) ^ 4 * inverseRadius8 (12688 - 1) /
            envelopeGap 12688 (61 / 100) 163 (17 / (100 * 12688)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12688

namespace BstLean.Part266.Row12688
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12688 163 ≤ (4593545719 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12688 163 ≤ (38312117 / 25000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (368333273 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12688 163 ≤ (459601441 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12688 163 ≤ (326997651 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12688 163 ≤ (477906911 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (95580383 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (95580383 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1506626489 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (103133739 / 20000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1830197 / 500000000) : ℝ) ≤ √(17 / (100 * 12688) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12688) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (437219357 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9703821699 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12688) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12688) ≤ (27865179 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12688) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12688 * (163 : ℝ) ^ 2 + 26 / (10 * 12688) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12688) : ℝ)) (tA 12688 * 163 ^ 2 + 26 / (10 * 12688)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1830197 / 500000000))) * ((95580383 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1830197 / 500000000)) ^ 3) * ((1506626489 / 1000000000000000000000000))) + ((103133739 / 20000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1830197 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12688) : ℝ)) d.D d.V d.P (√(tA 12688) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1830197 / 500000000)) ^ 2 * (((437219357 / 200000000000000)) * ((9703821699 / 250000000000000000)))) + ((103133739 / 20000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12688) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1830197 / 500000000)) * ((95580383 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12688) : ℝ)) (tA 12688 * 163 ^ 2 + 26 / (10 * 12688)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((95580383 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1830197 / 500000000)) ^ 2) * ((1506626489 / 1000000000000000000000000)) + ((103133739 / 20000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12688) : ℝ)) (√(26 / (10 * 12688) : ℝ)) d.D d.V d.P (√(tA 12688) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1830197 / 500000000)) * (((437219357 / 200000000000000)) * ((9703821699 / 250000000000000000))) + ((103133739 / 20000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12688) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((95580383 / 20000000000000000000) : ℝ) + ((103133739 / 20000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12688

namespace BstLean.Part266.Row12688
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12688 163 ∧
    0 ≤ (tableEnvelope C).f1 12688 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12688 163 ∧
    0 ≤ (tableEnvelope C).w1 12688 163 ∧ 0 ≤ (tableEnvelope C).w2 12688 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12688 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12688 163 ∧ 0 ≤ d.f1 12688 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12688 163 ∧ 0 ≤ d.w1 12688 163 ∧ 0 ≤ d.w2 12688 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12688 ≤ 2 * (228 / 100 : ℝ) / 12688 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12688 ≤ 2 * (370 / 100 : ℝ) / 12688 := by
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
    (completeRAData (tableEnvelope C) 12688 163).locationBound 12688 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12688 163).energyBound 12688 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12688 163) (d.f1 12688 163) d.f2 ≤
      32 * (((4593545719 / 1000000000000000000) : ℝ) + (38312117 / 25000000000000000) + (368333273 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12688 163) (d.w1 12688 163)
      (d.w2 12688 163) ≤
      32 * (((459601441 / 25000000000000000000) : ℝ) + (326997651 / 25000000000000000000) + (477906911 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12688 163) (d.f1 12688 163) d.f2 ≤
      ((4593545719 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4593545719 / 1000000000000000000)) * ((38312117 / 25000000000000000)) * (126 / 100) +
      2 * (((38312117 / 25000000000000000)) ^ 2 + 2 * ((4593545719 / 1000000000000000000)) * ((368333273 / 1000000000000000000))) +
      6 * ((38312117 / 25000000000000000)) * ((368333273 / 1000000000000000000)) * (126 / 100) + 8 * ((368333273 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12688 163) (d.f1 12688 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12688 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12688 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12688 163) (d.f1 12688 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12688 163) (d.w1 12688 163) (d.w2 12688 163)
  have hwexpr0 : 0 ≤ d.w0 12688 163 + d.w1 12688 163 * √(π / 2) +
      2 * d.w2 12688 163 + energyR16 12688 *
      radiusPolynomialRoot16 (d.w0 12688 163) (d.w1 12688 163) (d.w2 12688 163) := by
    positivity
  constructor
  · change (12688 : ℝ) ^ 8 * (mA 12688 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12688 163) (d.f1 12688 163) d.f2 + locationR16 12688 *
        radiusPolynomialRoot16 (d.f0 12688 163) (d.f1 12688 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12688 : ℝ) ^ 8 * (mA 12688 : ℝ) ^ 8 *
        ((((4593545719 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4593545719 / 1000000000000000000)) * ((38312117 / 25000000000000000)) * (126 / 100) +
          2 * (((38312117 / 25000000000000000)) ^ 2 + 2 * ((4593545719 / 1000000000000000000)) * ((368333273 / 1000000000000000000))) +
          6 * ((38312117 / 25000000000000000)) * ((368333273 / 1000000000000000000)) * (126 / 100) + 8 * ((368333273 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12688) *
          (32 * (((4593545719 / 1000000000000000000) : ℝ) + (38312117 / 25000000000000000) + (368333273 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12688 : ℝ) ^ 16 *
      (d.w0 12688 163 + d.w1 12688 163 * √(π / 2) + 2 * d.w2 12688 163 +
        energyR16 12688 * radiusPolynomialRoot16 (d.w0 12688 163) (d.w1 12688 163)
          (d.w2 12688 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12688 : ℝ) ^ 16 *
        (((459601441 / 25000000000000000000) : ℝ) + ((326997651 / 25000000000000000000)) * (126 / 100) + 2 * ((477906911 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12688) *
          (32 * (((459601441 / 25000000000000000000) : ℝ) + (326997651 / 25000000000000000000) + (477906911 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12688

/-! A coarse bound on the actual paper statistics constant at dimension 12689. -/
namespace BstLean.Part266.Row12689
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12687 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12687 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12687 128 ≤ (12941 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12941 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12689) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12689 : ℕ))
    (by norm_num : (12689 : ℕ) ≤ 16384)
  have ht : paperTail256 12689 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12689 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12689 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12689 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12689 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12689 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12687 128 * √(2 / (12689 : ℝ)) *
      (√(12689 : ℝ) + paperT0 12689 + paperTail256 12689) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12689 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12689 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12689 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12687 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12687 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12689 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12689

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12689
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12689 (61 / 100) 163 (17 / (100 * 12689)) (26 / (10 * 12689)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12689 (61 / 100) 163 (17 / (100 * 12689)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (47778893 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1506151587 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5153405017 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12689 / 12689 * (61 / 100)) ^ 4 * inverseRadius8 (12689 - 1) /
            envelopeGap 12689 (61 / 100) 163 (17 / (100 * 12689)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12689

namespace BstLean.Part266.Row12689
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12689 163 ≤ (4592639829 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12689 163 ≤ (383045637 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (368260679 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12689 163 ≤ (1837970953 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12689 163 ≤ (326920321 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12689 163 ≤ (477793923 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (47778893 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (47778893 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1506151587 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5153405017 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((14641 / 4000000) : ℝ) ≤ √(17 / (100 * 12689) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12689) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (136614897 / 62500000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38809168853 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12689) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12689) ≤ (27862983 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12689) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12689 * (163 : ℝ) ^ 2 + 26 / (10 * 12689) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12689) : ℝ)) (tA 12689 * 163 ^ 2 + 26 / (10 * 12689)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((14641 / 4000000))) * ((47778893 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((14641 / 4000000)) ^ 3) * ((1506151587 / 1000000000000000000000000))) + ((5153405017 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((14641 / 4000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12689) : ℝ)) d.D d.V d.P (√(tA 12689) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((14641 / 4000000)) ^ 2 * (((136614897 / 62500000000000)) * ((38809168853 / 1000000000000000000)))) + ((5153405017 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12689) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((14641 / 4000000)) * ((47778893 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12689) : ℝ)) (tA 12689 * 163 ^ 2 + 26 / (10 * 12689)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((47778893 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((14641 / 4000000)) ^ 2) * ((1506151587 / 1000000000000000000000000)) + ((5153405017 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12689) : ℝ)) (√(26 / (10 * 12689) : ℝ)) d.D d.V d.P (√(tA 12689) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((14641 / 4000000)) * (((136614897 / 62500000000000)) * ((38809168853 / 1000000000000000000))) + ((5153405017 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12689) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((47778893 / 10000000000000000000) : ℝ) + ((5153405017 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12689

namespace BstLean.Part266.Row12689
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12689 163 ∧
    0 ≤ (tableEnvelope C).f1 12689 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12689 163 ∧
    0 ≤ (tableEnvelope C).w1 12689 163 ∧ 0 ≤ (tableEnvelope C).w2 12689 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12689 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12689 163 ∧ 0 ≤ d.f1 12689 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12689 163 ∧ 0 ≤ d.w1 12689 163 ∧ 0 ≤ d.w2 12689 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12689 ≤ 2 * (228 / 100 : ℝ) / 12689 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12689 ≤ 2 * (370 / 100 : ℝ) / 12689 := by
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
    (completeRAData (tableEnvelope C) 12689 163).locationBound 12689 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12689 163).energyBound 12689 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12689 163) (d.f1 12689 163) d.f2 ≤
      32 * (((4592639829 / 1000000000000000000) : ℝ) + (383045637 / 250000000000000000) + (368260679 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12689 163) (d.w1 12689 163)
      (d.w2 12689 163) ≤
      32 * (((1837970953 / 100000000000000000000) : ℝ) + (326920321 / 25000000000000000000) + (477793923 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12689 163) (d.f1 12689 163) d.f2 ≤
      ((4592639829 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4592639829 / 1000000000000000000)) * ((383045637 / 250000000000000000)) * (126 / 100) +
      2 * (((383045637 / 250000000000000000)) ^ 2 + 2 * ((4592639829 / 1000000000000000000)) * ((368260679 / 1000000000000000000))) +
      6 * ((383045637 / 250000000000000000)) * ((368260679 / 1000000000000000000)) * (126 / 100) + 8 * ((368260679 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12689 163) (d.f1 12689 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12689 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12689 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12689 163) (d.f1 12689 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12689 163) (d.w1 12689 163) (d.w2 12689 163)
  have hwexpr0 : 0 ≤ d.w0 12689 163 + d.w1 12689 163 * √(π / 2) +
      2 * d.w2 12689 163 + energyR16 12689 *
      radiusPolynomialRoot16 (d.w0 12689 163) (d.w1 12689 163) (d.w2 12689 163) := by
    positivity
  constructor
  · change (12689 : ℝ) ^ 8 * (mA 12689 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12689 163) (d.f1 12689 163) d.f2 + locationR16 12689 *
        radiusPolynomialRoot16 (d.f0 12689 163) (d.f1 12689 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12689 : ℝ) ^ 8 * (mA 12689 : ℝ) ^ 8 *
        ((((4592639829 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4592639829 / 1000000000000000000)) * ((383045637 / 250000000000000000)) * (126 / 100) +
          2 * (((383045637 / 250000000000000000)) ^ 2 + 2 * ((4592639829 / 1000000000000000000)) * ((368260679 / 1000000000000000000))) +
          6 * ((383045637 / 250000000000000000)) * ((368260679 / 1000000000000000000)) * (126 / 100) + 8 * ((368260679 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12689) *
          (32 * (((4592639829 / 1000000000000000000) : ℝ) + (383045637 / 250000000000000000) + (368260679 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12689 : ℝ) ^ 16 *
      (d.w0 12689 163 + d.w1 12689 163 * √(π / 2) + 2 * d.w2 12689 163 +
        energyR16 12689 * radiusPolynomialRoot16 (d.w0 12689 163) (d.w1 12689 163)
          (d.w2 12689 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12689 : ℝ) ^ 16 *
        (((1837970953 / 100000000000000000000) : ℝ) + ((326920321 / 25000000000000000000)) * (126 / 100) + 2 * ((477793923 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12689) *
          (32 * (((1837970953 / 100000000000000000000) : ℝ) + (326920321 / 25000000000000000000) + (477793923 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12689

/-! A coarse bound on the actual paper statistics constant at dimension 12690. -/
namespace BstLean.Part266.Row12690
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12688 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12688 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12688 128 ≤ (12942 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12942 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12690) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12690 : ℕ))
    (by norm_num : (12690 : ℕ) ≤ 16384)
  have ht : paperTail256 12690 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12690 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12690 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12690 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12690 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12690 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12688 128 * √(2 / (12690 : ℝ)) *
      (√(12690 : ℝ) + paperT0 12690 + paperTail256 12690) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12690 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12690 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12690 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12688 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12688 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12690 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12690

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12690
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12690 (61 / 100) 163 (17 / (100 * 12690)) (26 / (10 * 12690)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12690 (61 / 100) 163 (17 / (100 * 12690)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (477675981 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (188209609 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1287531359 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12690 / 12690 * (61 / 100)) ^ 4 * inverseRadius8 (12690 - 1) /
            envelopeGap 12690 (61 / 100) 163 (17 / (100 * 12690)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12690

namespace BstLean.Part266.Row12690
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12690 163 ≤ (286983617 / 62500000000000000)
  f1 : (tableEnvelope C).f1 12690 163 ≤ (1531881351 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (23011763 / 62500000000000000)
  w0 : (tableEnvelope C).w0 12690 163 ≤ (367507407 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12690 163 ≤ (1307372427 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12690 163 ≤ (47768097 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (477675981 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (477675981 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (188209609 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1287531359 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((732021 / 200000000) : ℝ) ≤ √(17 / (100 * 12690) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12690) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (546394993 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7760610471 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12690) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12690) ≤ (2228863 / 20000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12690) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12690 * (163 : ℝ) ^ 2 + 26 / (10 * 12690) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12690) : ℝ)) (tA 12690 * 163 ^ 2 + 26 / (10 * 12690)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((732021 / 200000000))) * ((477675981 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((732021 / 200000000)) ^ 3) * ((188209609 / 125000000000000000000000))) + ((1287531359 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((732021 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12690) : ℝ)) d.D d.V d.P (√(tA 12690) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((732021 / 200000000)) ^ 2 * (((546394993 / 250000000000000)) * ((7760610471 / 200000000000000000)))) + ((1287531359 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12690) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((732021 / 200000000)) * ((477675981 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12690) : ℝ)) (tA 12690 * 163 ^ 2 + 26 / (10 * 12690)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((477675981 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((732021 / 200000000)) ^ 2) * ((188209609 / 125000000000000000000000)) + ((1287531359 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12690) : ℝ)) (√(26 / (10 * 12690) : ℝ)) d.D d.V d.P (√(tA 12690) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((732021 / 200000000)) * (((546394993 / 250000000000000)) * ((7760610471 / 200000000000000000))) + ((1287531359 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12690) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((477675981 / 100000000000000000000) : ℝ) + ((1287531359 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12690

namespace BstLean.Part266.Row12690
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12690 163 ∧
    0 ≤ (tableEnvelope C).f1 12690 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12690 163 ∧
    0 ≤ (tableEnvelope C).w1 12690 163 ∧ 0 ≤ (tableEnvelope C).w2 12690 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12690 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12690 163 ∧ 0 ≤ d.f1 12690 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12690 163 ∧ 0 ≤ d.w1 12690 163 ∧ 0 ≤ d.w2 12690 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12690 ≤ 2 * (228 / 100 : ℝ) / 12690 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12690 ≤ 2 * (370 / 100 : ℝ) / 12690 := by
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
    (completeRAData (tableEnvelope C) 12690 163).locationBound 12690 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12690 163).energyBound 12690 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12690 163) (d.f1 12690 163) d.f2 ≤
      32 * (((286983617 / 62500000000000000) : ℝ) + (1531881351 / 1000000000000000000) + (23011763 / 62500000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12690 163) (d.w1 12690 163)
      (d.w2 12690 163) ≤
      32 * (((367507407 / 20000000000000000000) : ℝ) + (1307372427 / 100000000000000000000) + (47768097 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12690 163) (d.f1 12690 163) d.f2 ≤
      ((286983617 / 62500000000000000) : ℝ) ^ 2 + 2 * ((286983617 / 62500000000000000)) * ((1531881351 / 1000000000000000000)) * (126 / 100) +
      2 * (((1531881351 / 1000000000000000000)) ^ 2 + 2 * ((286983617 / 62500000000000000)) * ((23011763 / 62500000000000000))) +
      6 * ((1531881351 / 1000000000000000000)) * ((23011763 / 62500000000000000)) * (126 / 100) + 8 * ((23011763 / 62500000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12690 163) (d.f1 12690 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12690 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12690 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12690 163) (d.f1 12690 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12690 163) (d.w1 12690 163) (d.w2 12690 163)
  have hwexpr0 : 0 ≤ d.w0 12690 163 + d.w1 12690 163 * √(π / 2) +
      2 * d.w2 12690 163 + energyR16 12690 *
      radiusPolynomialRoot16 (d.w0 12690 163) (d.w1 12690 163) (d.w2 12690 163) := by
    positivity
  constructor
  · change (12690 : ℝ) ^ 8 * (mA 12690 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12690 163) (d.f1 12690 163) d.f2 + locationR16 12690 *
        radiusPolynomialRoot16 (d.f0 12690 163) (d.f1 12690 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12690 : ℝ) ^ 8 * (mA 12690 : ℝ) ^ 8 *
        ((((286983617 / 62500000000000000) : ℝ) ^ 2 + 2 * ((286983617 / 62500000000000000)) * ((1531881351 / 1000000000000000000)) * (126 / 100) +
          2 * (((1531881351 / 1000000000000000000)) ^ 2 + 2 * ((286983617 / 62500000000000000)) * ((23011763 / 62500000000000000))) +
          6 * ((1531881351 / 1000000000000000000)) * ((23011763 / 62500000000000000)) * (126 / 100) + 8 * ((23011763 / 62500000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12690) *
          (32 * (((286983617 / 62500000000000000) : ℝ) + (1531881351 / 1000000000000000000) + (23011763 / 62500000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12690 : ℝ) ^ 16 *
      (d.w0 12690 163 + d.w1 12690 163 * √(π / 2) + 2 * d.w2 12690 163 +
        energyR16 12690 * radiusPolynomialRoot16 (d.w0 12690 163) (d.w1 12690 163)
          (d.w2 12690 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12690 : ℝ) ^ 16 *
        (((367507407 / 20000000000000000000) : ℝ) + ((1307372427 / 100000000000000000000)) * (126 / 100) + 2 * ((47768097 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12690) *
          (32 * (((367507407 / 20000000000000000000) : ℝ) + (1307372427 / 100000000000000000000) + (47768097 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12690

/-! A coarse bound on the actual paper statistics constant at dimension 12691. -/
namespace BstLean.Part266.Row12691
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12689 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12689 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12689 128 ≤ (12943 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12943 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12691) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12691 : ℕ))
    (by norm_num : (12691 : ℕ) ≤ 16384)
  have ht : paperTail256 12691 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12691 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12691 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12691 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12691 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12691 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12689 128 * √(2 / (12691 : ℝ)) *
      (√(12691 : ℝ) + paperT0 12691 + paperTail256 12691) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12691 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12691 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12691 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12689 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12689 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12691 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12691

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12691
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12691 (61 / 100) 163 (17 / (100 * 12691)) (26 / (10 * 12691)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12691 (61 / 100) 163 (17 / (100 * 12691)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (477563067 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (188150293 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2573424103 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12691 / 12691 * (61 / 100)) ^ 4 * inverseRadius8 (12691 - 1) /
            envelopeGap 12691 (61 / 100) 163 (17 / (100 * 12691)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12691

namespace BstLean.Part266.Row12691
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12691 163 ≤ (1147708151 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12691 163 ≤ (1531579413 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (184057829 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12691 163 ≤ (918551261 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12691 163 ≤ (653531657 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12691 163 ≤ (477568053 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (477563067 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (477563067 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (188150293 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2573424103 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3659961 / 1000000000) : ℝ) ≤ √(17 / (100 * 12691) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12691) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (54633041 / 25000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19398468651 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12691) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12691) ≤ (870581 / 7812500000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12691) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12691 * (163 : ℝ) ^ 2 + 26 / (10 * 12691) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12691) : ℝ)) (tA 12691 * 163 ^ 2 + 26 / (10 * 12691)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3659961 / 1000000000))) * ((477563067 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3659961 / 1000000000)) ^ 3) * ((188150293 / 125000000000000000000000))) + ((2573424103 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3659961 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12691) : ℝ)) d.D d.V d.P (√(tA 12691) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3659961 / 1000000000)) ^ 2 * (((54633041 / 25000000000000)) * ((19398468651 / 500000000000000000)))) + ((2573424103 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12691) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3659961 / 1000000000)) * ((477563067 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12691) : ℝ)) (tA 12691 * 163 ^ 2 + 26 / (10 * 12691)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((477563067 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3659961 / 1000000000)) ^ 2) * ((188150293 / 125000000000000000000000)) + ((2573424103 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12691) : ℝ)) (√(26 / (10 * 12691) : ℝ)) d.D d.V d.P (√(tA 12691) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3659961 / 1000000000)) * (((54633041 / 25000000000000)) * ((19398468651 / 500000000000000000))) + ((2573424103 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12691) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((477563067 / 100000000000000000000) : ℝ) + ((2573424103 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12691

namespace BstLean.Part266.Row12691
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12691 163 ∧
    0 ≤ (tableEnvelope C).f1 12691 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12691 163 ∧
    0 ≤ (tableEnvelope C).w1 12691 163 ∧ 0 ≤ (tableEnvelope C).w2 12691 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12691 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12691 163 ∧ 0 ≤ d.f1 12691 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12691 163 ∧ 0 ≤ d.w1 12691 163 ∧ 0 ≤ d.w2 12691 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12691 ≤ 2 * (228 / 100 : ℝ) / 12691 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12691 ≤ 2 * (370 / 100 : ℝ) / 12691 := by
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
    (completeRAData (tableEnvelope C) 12691 163).locationBound 12691 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12691 163).energyBound 12691 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12691 163) (d.f1 12691 163) d.f2 ≤
      32 * (((1147708151 / 250000000000000000) : ℝ) + (1531579413 / 1000000000000000000) + (184057829 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12691 163) (d.w1 12691 163)
      (d.w2 12691 163) ≤
      32 * (((918551261 / 50000000000000000000) : ℝ) + (653531657 / 50000000000000000000) + (477568053 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12691 163) (d.f1 12691 163) d.f2 ≤
      ((1147708151 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1147708151 / 250000000000000000)) * ((1531579413 / 1000000000000000000)) * (126 / 100) +
      2 * (((1531579413 / 1000000000000000000)) ^ 2 + 2 * ((1147708151 / 250000000000000000)) * ((184057829 / 500000000000000000))) +
      6 * ((1531579413 / 1000000000000000000)) * ((184057829 / 500000000000000000)) * (126 / 100) + 8 * ((184057829 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12691 163) (d.f1 12691 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12691 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12691 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12691 163) (d.f1 12691 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12691 163) (d.w1 12691 163) (d.w2 12691 163)
  have hwexpr0 : 0 ≤ d.w0 12691 163 + d.w1 12691 163 * √(π / 2) +
      2 * d.w2 12691 163 + energyR16 12691 *
      radiusPolynomialRoot16 (d.w0 12691 163) (d.w1 12691 163) (d.w2 12691 163) := by
    positivity
  constructor
  · change (12691 : ℝ) ^ 8 * (mA 12691 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12691 163) (d.f1 12691 163) d.f2 + locationR16 12691 *
        radiusPolynomialRoot16 (d.f0 12691 163) (d.f1 12691 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12691 : ℝ) ^ 8 * (mA 12691 : ℝ) ^ 8 *
        ((((1147708151 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1147708151 / 250000000000000000)) * ((1531579413 / 1000000000000000000)) * (126 / 100) +
          2 * (((1531579413 / 1000000000000000000)) ^ 2 + 2 * ((1147708151 / 250000000000000000)) * ((184057829 / 500000000000000000))) +
          6 * ((1531579413 / 1000000000000000000)) * ((184057829 / 500000000000000000)) * (126 / 100) + 8 * ((184057829 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12691) *
          (32 * (((1147708151 / 250000000000000000) : ℝ) + (1531579413 / 1000000000000000000) + (184057829 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12691 : ℝ) ^ 16 *
      (d.w0 12691 163 + d.w1 12691 163 * √(π / 2) + 2 * d.w2 12691 163 +
        energyR16 12691 * radiusPolynomialRoot16 (d.w0 12691 163) (d.w1 12691 163)
          (d.w2 12691 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12691 : ℝ) ^ 16 *
        (((918551261 / 50000000000000000000) : ℝ) + ((653531657 / 50000000000000000000)) * (126 / 100) + 2 * ((477568053 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12691) *
          (32 * (((918551261 / 50000000000000000000) : ℝ) + (653531657 / 50000000000000000000) + (477568053 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12691

/-! A coarse bound on the actual paper statistics constant at dimension 12692. -/
namespace BstLean.Part266.Row12692
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12690 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12690 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12690 128 ≤ (12944 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12944 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12692) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12692 : ℕ))
    (by norm_num : (12692 : ℕ) ≤ 16384)
  have ht : paperTail256 12692 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12692 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12692 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12692 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12692 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12692 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12690 128 * √(2 / (12692 : ℝ)) *
      (√(12692 : ℝ) + paperT0 12692 + paperTail256 12692) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12692 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12692 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12692 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12690 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12690 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12692 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12692

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12692
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12692 (61 / 100) 163 (17 / (100 * 12692)) (26 / (10 * 12692)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12692 (61 / 100) 163 (17 / (100 * 12692)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (477450189 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1504728003 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1285893331 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12692 / 12692 * (61 / 100)) ^ 4 * inverseRadius8 (12692 - 1) /
            envelopeGap 12692 (61 / 100) 163 (17 / (100 * 12692)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12692

namespace BstLean.Part266.Row12692
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12692 163 ≤ (143435239 / 31250000000000000)
  f1 : (tableEnvelope C).f1 12692 163 ≤ (765638787 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (36804313 / 100000000000000000)
  w0 : (tableEnvelope C).w0 12692 163 ≤ (1434897 / 78125000000000000)
  w1 : (tableEnvelope C).w1 12692 163 ≤ (653377153 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12692 163 ≤ (119363793 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (477450189 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (477450189 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1504728003 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1285893331 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3659817 / 1000000000) : ℝ) ≤ √(17 / (100 * 12692) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12692) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2185063361 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (2424426481 / 62500000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12692) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12692) ≤ (27856397 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12692) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12692 * (163 : ℝ) ^ 2 + 26 / (10 * 12692) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12692) : ℝ)) (tA 12692 * 163 ^ 2 + 26 / (10 * 12692)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3659817 / 1000000000))) * ((477450189 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3659817 / 1000000000)) ^ 3) * ((1504728003 / 1000000000000000000000000))) + ((1285893331 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3659817 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12692) : ℝ)) d.D d.V d.P (√(tA 12692) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3659817 / 1000000000)) ^ 2 * (((2185063361 / 1000000000000000)) * ((2424426481 / 62500000000000000)))) + ((1285893331 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12692) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3659817 / 1000000000)) * ((477450189 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12692) : ℝ)) (tA 12692 * 163 ^ 2 + 26 / (10 * 12692)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((477450189 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3659817 / 1000000000)) ^ 2) * ((1504728003 / 1000000000000000000000000)) + ((1285893331 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12692) : ℝ)) (√(26 / (10 * 12692) : ℝ)) d.D d.V d.P (√(tA 12692) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3659817 / 1000000000)) * (((2185063361 / 1000000000000000)) * ((2424426481 / 62500000000000000))) + ((1285893331 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12692) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((477450189 / 100000000000000000000) : ℝ) + ((1285893331 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12692

namespace BstLean.Part266.Row12692
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12692 163 ∧
    0 ≤ (tableEnvelope C).f1 12692 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12692 163 ∧
    0 ≤ (tableEnvelope C).w1 12692 163 ∧ 0 ≤ (tableEnvelope C).w2 12692 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12692 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12692 163 ∧ 0 ≤ d.f1 12692 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12692 163 ∧ 0 ≤ d.w1 12692 163 ∧ 0 ≤ d.w2 12692 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12692 ≤ 2 * (228 / 100 : ℝ) / 12692 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12692 ≤ 2 * (370 / 100 : ℝ) / 12692 := by
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
    (completeRAData (tableEnvelope C) 12692 163).locationBound 12692 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12692 163).energyBound 12692 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12692 163) (d.f1 12692 163) d.f2 ≤
      32 * (((143435239 / 31250000000000000) : ℝ) + (765638787 / 500000000000000000) + (36804313 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12692 163) (d.w1 12692 163)
      (d.w2 12692 163) ≤
      32 * (((1434897 / 78125000000000000) : ℝ) + (653377153 / 50000000000000000000) + (119363793 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12692 163) (d.f1 12692 163) d.f2 ≤
      ((143435239 / 31250000000000000) : ℝ) ^ 2 + 2 * ((143435239 / 31250000000000000)) * ((765638787 / 500000000000000000)) * (126 / 100) +
      2 * (((765638787 / 500000000000000000)) ^ 2 + 2 * ((143435239 / 31250000000000000)) * ((36804313 / 100000000000000000))) +
      6 * ((765638787 / 500000000000000000)) * ((36804313 / 100000000000000000)) * (126 / 100) + 8 * ((36804313 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12692 163) (d.f1 12692 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12692 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12692 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12692 163) (d.f1 12692 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12692 163) (d.w1 12692 163) (d.w2 12692 163)
  have hwexpr0 : 0 ≤ d.w0 12692 163 + d.w1 12692 163 * √(π / 2) +
      2 * d.w2 12692 163 + energyR16 12692 *
      radiusPolynomialRoot16 (d.w0 12692 163) (d.w1 12692 163) (d.w2 12692 163) := by
    positivity
  constructor
  · change (12692 : ℝ) ^ 8 * (mA 12692 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12692 163) (d.f1 12692 163) d.f2 + locationR16 12692 *
        radiusPolynomialRoot16 (d.f0 12692 163) (d.f1 12692 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12692 : ℝ) ^ 8 * (mA 12692 : ℝ) ^ 8 *
        ((((143435239 / 31250000000000000) : ℝ) ^ 2 + 2 * ((143435239 / 31250000000000000)) * ((765638787 / 500000000000000000)) * (126 / 100) +
          2 * (((765638787 / 500000000000000000)) ^ 2 + 2 * ((143435239 / 31250000000000000)) * ((36804313 / 100000000000000000))) +
          6 * ((765638787 / 500000000000000000)) * ((36804313 / 100000000000000000)) * (126 / 100) + 8 * ((36804313 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12692) *
          (32 * (((143435239 / 31250000000000000) : ℝ) + (765638787 / 500000000000000000) + (36804313 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12692 : ℝ) ^ 16 *
      (d.w0 12692 163 + d.w1 12692 163 * √(π / 2) + 2 * d.w2 12692 163 +
        energyR16 12692 * radiusPolynomialRoot16 (d.w0 12692 163) (d.w1 12692 163)
          (d.w2 12692 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12692 : ℝ) ^ 16 *
        (((1434897 / 78125000000000000) : ℝ) + ((653377153 / 50000000000000000000)) * (126 / 100) + 2 * ((119363793 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12692) *
          (32 * (((1434897 / 78125000000000000) : ℝ) + (653377153 / 50000000000000000000) + (119363793 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12692

/-! A coarse bound on the actual paper statistics constant at dimension 12693. -/
namespace BstLean.Part266.Row12693
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12691 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12691 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12691 128 ≤ (12945 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12945 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12693) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12693 : ℕ))
    (by norm_num : (12693 : ℕ) ≤ 16384)
  have ht : paperTail256 12693 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12693 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12693 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12693 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12693 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12693 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12691 128 * √(2 / (12693 : ℝ)) *
      (√(12693 : ℝ) + paperT0 12693 + paperTail256 12693) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12693 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12693 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12693 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12691 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12691 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12693 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12693

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12693
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12693 (61 / 100) 163 (17 / (100 * 12693)) (26 / (10 * 12693)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12693 (61 / 100) 163 (17 / (100 * 12693)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (238668673 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1504253849 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1285075197 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12693 / 12693 * (61 / 100)) ^ 4 * inverseRadius8 (12693 - 1) /
            envelopeGap 12693 (61 / 100) 163 (17 / (100 * 12693)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12693

namespace BstLean.Part266.Row12693
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12693 163 ≤ (4589023003 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12693 163 ≤ (191371979 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (367970623 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12693 163 ≤ (1836233947 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12693 163 ≤ (1306445401 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12693 163 ≤ (238671163 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (238668673 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (238668673 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1504253849 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1285075197 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3659673 / 1000000000) : ℝ) ≤ √(17 / (100 * 12693) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12693) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2184805131 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38784711537 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12693) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12693) ≤ (11141681 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12693) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12693 * (163 : ℝ) ^ 2 + 26 / (10 * 12693) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12693) : ℝ)) (tA 12693 * 163 ^ 2 + 26 / (10 * 12693)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3659673 / 1000000000))) * ((238668673 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3659673 / 1000000000)) ^ 3) * ((1504253849 / 1000000000000000000000000))) + ((1285075197 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3659673 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12693) : ℝ)) d.D d.V d.P (√(tA 12693) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3659673 / 1000000000)) ^ 2 * (((2184805131 / 1000000000000000)) * ((38784711537 / 1000000000000000000)))) + ((1285075197 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12693) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3659673 / 1000000000)) * ((238668673 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12693) : ℝ)) (tA 12693 * 163 ^ 2 + 26 / (10 * 12693)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((238668673 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3659673 / 1000000000)) ^ 2) * ((1504253849 / 1000000000000000000000000)) + ((1285075197 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12693) : ℝ)) (√(26 / (10 * 12693) : ℝ)) d.D d.V d.P (√(tA 12693) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3659673 / 1000000000)) * (((2184805131 / 1000000000000000)) * ((38784711537 / 1000000000000000000))) + ((1285075197 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12693) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((238668673 / 50000000000000000000) : ℝ) + ((1285075197 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12693

namespace BstLean.Part266.Row12693
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12693 163 ∧
    0 ≤ (tableEnvelope C).f1 12693 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12693 163 ∧
    0 ≤ (tableEnvelope C).w1 12693 163 ∧ 0 ≤ (tableEnvelope C).w2 12693 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12693 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12693 163 ∧ 0 ≤ d.f1 12693 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12693 163 ∧ 0 ≤ d.w1 12693 163 ∧ 0 ≤ d.w2 12693 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12693 ≤ 2 * (228 / 100 : ℝ) / 12693 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12693 ≤ 2 * (370 / 100 : ℝ) / 12693 := by
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
    (completeRAData (tableEnvelope C) 12693 163).locationBound 12693 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12693 163).energyBound 12693 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12693 163) (d.f1 12693 163) d.f2 ≤
      32 * (((4589023003 / 1000000000000000000) : ℝ) + (191371979 / 125000000000000000) + (367970623 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12693 163) (d.w1 12693 163)
      (d.w2 12693 163) ≤
      32 * (((1836233947 / 100000000000000000000) : ℝ) + (1306445401 / 100000000000000000000) + (238671163 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12693 163) (d.f1 12693 163) d.f2 ≤
      ((4589023003 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4589023003 / 1000000000000000000)) * ((191371979 / 125000000000000000)) * (126 / 100) +
      2 * (((191371979 / 125000000000000000)) ^ 2 + 2 * ((4589023003 / 1000000000000000000)) * ((367970623 / 1000000000000000000))) +
      6 * ((191371979 / 125000000000000000)) * ((367970623 / 1000000000000000000)) * (126 / 100) + 8 * ((367970623 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12693 163) (d.f1 12693 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12693 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12693 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12693 163) (d.f1 12693 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12693 163) (d.w1 12693 163) (d.w2 12693 163)
  have hwexpr0 : 0 ≤ d.w0 12693 163 + d.w1 12693 163 * √(π / 2) +
      2 * d.w2 12693 163 + energyR16 12693 *
      radiusPolynomialRoot16 (d.w0 12693 163) (d.w1 12693 163) (d.w2 12693 163) := by
    positivity
  constructor
  · change (12693 : ℝ) ^ 8 * (mA 12693 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12693 163) (d.f1 12693 163) d.f2 + locationR16 12693 *
        radiusPolynomialRoot16 (d.f0 12693 163) (d.f1 12693 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12693 : ℝ) ^ 8 * (mA 12693 : ℝ) ^ 8 *
        ((((4589023003 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4589023003 / 1000000000000000000)) * ((191371979 / 125000000000000000)) * (126 / 100) +
          2 * (((191371979 / 125000000000000000)) ^ 2 + 2 * ((4589023003 / 1000000000000000000)) * ((367970623 / 1000000000000000000))) +
          6 * ((191371979 / 125000000000000000)) * ((367970623 / 1000000000000000000)) * (126 / 100) + 8 * ((367970623 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12693) *
          (32 * (((4589023003 / 1000000000000000000) : ℝ) + (191371979 / 125000000000000000) + (367970623 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12693 : ℝ) ^ 16 *
      (d.w0 12693 163 + d.w1 12693 163 * √(π / 2) + 2 * d.w2 12693 163 +
        energyR16 12693 * radiusPolynomialRoot16 (d.w0 12693 163) (d.w1 12693 163)
          (d.w2 12693 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12693 : ℝ) ^ 16 *
        (((1836233947 / 100000000000000000000) : ℝ) + ((1306445401 / 100000000000000000000)) * (126 / 100) + 2 * ((238671163 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12693) *
          (32 * (((1836233947 / 100000000000000000000) : ℝ) + (1306445401 / 100000000000000000000) + (238671163 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12693

/-! A coarse bound on the actual paper statistics constant at dimension 12694. -/
namespace BstLean.Part266.Row12694
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12692 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12692 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12692 128 ≤ (12946 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12946 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12694) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12694 : ℕ))
    (by norm_num : (12694 : ℕ) ≤ 16384)
  have ht : paperTail256 12694 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12694 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12694 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12694 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12694 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12694 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12692 128 * √(2 / (12694 : ℝ)) *
      (√(12694 : ℝ) + paperT0 12694 + paperTail256 12694) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12694 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12694 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12694 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12692 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12692 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12694 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12694

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12694
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12694 (61 / 100) 163 (17 / (100 * 12694)) (26 / (10 * 12694)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12694 (61 / 100) 163 (17 / (100 * 12694)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (477224539 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (751889941 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5137030597 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12694 / 12694 * (61 / 100)) ^ 4 * inverseRadius8 (12694 - 1) /
            envelopeGap 12694 (61 / 100) 163 (17 / (100 * 12694)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12694

namespace BstLean.Part266.Row12694
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12694 163 ≤ (458811867 / 100000000000000000)
  f1 : (tableEnvelope C).f1 12694 163 ≤ (382668547 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (183949069 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12694 163 ≤ (458949971 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12694 163 ≤ (6530683 / 500000000000000000)
  w2 : (tableEnvelope C).w2 12694 163 ≤ (119307379 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (477224539 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (477224539 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (751889941 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5137030597 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3659529 / 1000000000) : ℝ) ≤ √(17 / (100 * 12694) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12694) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1092273477 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19389300413 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12694) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12694) ≤ (111408033 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12694) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12694 * (163 : ℝ) ^ 2 + 26 / (10 * 12694) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12694) : ℝ)) (tA 12694 * 163 ^ 2 + 26 / (10 * 12694)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3659529 / 1000000000))) * ((477224539 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3659529 / 1000000000)) ^ 3) * ((751889941 / 500000000000000000000000))) + ((5137030597 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3659529 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12694) : ℝ)) d.D d.V d.P (√(tA 12694) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3659529 / 1000000000)) ^ 2 * (((1092273477 / 500000000000000)) * ((19389300413 / 500000000000000000)))) + ((5137030597 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12694) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3659529 / 1000000000)) * ((477224539 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12694) : ℝ)) (tA 12694 * 163 ^ 2 + 26 / (10 * 12694)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((477224539 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3659529 / 1000000000)) ^ 2) * ((751889941 / 500000000000000000000000)) + ((5137030597 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12694) : ℝ)) (√(26 / (10 * 12694) : ℝ)) d.D d.V d.P (√(tA 12694) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3659529 / 1000000000)) * (((1092273477 / 500000000000000)) * ((19389300413 / 500000000000000000))) + ((5137030597 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12694) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((477224539 / 100000000000000000000) : ℝ) + ((5137030597 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12694

namespace BstLean.Part266.Row12694
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12694 163 ∧
    0 ≤ (tableEnvelope C).f1 12694 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12694 163 ∧
    0 ≤ (tableEnvelope C).w1 12694 163 ∧ 0 ≤ (tableEnvelope C).w2 12694 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12694 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12694 163 ∧ 0 ≤ d.f1 12694 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12694 163 ∧ 0 ≤ d.w1 12694 163 ∧ 0 ≤ d.w2 12694 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12694 ≤ 2 * (228 / 100 : ℝ) / 12694 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12694 ≤ 2 * (370 / 100 : ℝ) / 12694 := by
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
    (completeRAData (tableEnvelope C) 12694 163).locationBound 12694 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12694 163).energyBound 12694 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12694 163) (d.f1 12694 163) d.f2 ≤
      32 * (((458811867 / 100000000000000000) : ℝ) + (382668547 / 250000000000000000) + (183949069 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12694 163) (d.w1 12694 163)
      (d.w2 12694 163) ≤
      32 * (((458949971 / 25000000000000000000) : ℝ) + (6530683 / 500000000000000000) + (119307379 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12694 163) (d.f1 12694 163) d.f2 ≤
      ((458811867 / 100000000000000000) : ℝ) ^ 2 + 2 * ((458811867 / 100000000000000000)) * ((382668547 / 250000000000000000)) * (126 / 100) +
      2 * (((382668547 / 250000000000000000)) ^ 2 + 2 * ((458811867 / 100000000000000000)) * ((183949069 / 500000000000000000))) +
      6 * ((382668547 / 250000000000000000)) * ((183949069 / 500000000000000000)) * (126 / 100) + 8 * ((183949069 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12694 163) (d.f1 12694 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12694 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12694 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12694 163) (d.f1 12694 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12694 163) (d.w1 12694 163) (d.w2 12694 163)
  have hwexpr0 : 0 ≤ d.w0 12694 163 + d.w1 12694 163 * √(π / 2) +
      2 * d.w2 12694 163 + energyR16 12694 *
      radiusPolynomialRoot16 (d.w0 12694 163) (d.w1 12694 163) (d.w2 12694 163) := by
    positivity
  constructor
  · change (12694 : ℝ) ^ 8 * (mA 12694 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12694 163) (d.f1 12694 163) d.f2 + locationR16 12694 *
        radiusPolynomialRoot16 (d.f0 12694 163) (d.f1 12694 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12694 : ℝ) ^ 8 * (mA 12694 : ℝ) ^ 8 *
        ((((458811867 / 100000000000000000) : ℝ) ^ 2 + 2 * ((458811867 / 100000000000000000)) * ((382668547 / 250000000000000000)) * (126 / 100) +
          2 * (((382668547 / 250000000000000000)) ^ 2 + 2 * ((458811867 / 100000000000000000)) * ((183949069 / 500000000000000000))) +
          6 * ((382668547 / 250000000000000000)) * ((183949069 / 500000000000000000)) * (126 / 100) + 8 * ((183949069 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12694) *
          (32 * (((458811867 / 100000000000000000) : ℝ) + (382668547 / 250000000000000000) + (183949069 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12694 : ℝ) ^ 16 *
      (d.w0 12694 163 + d.w1 12694 163 * √(π / 2) + 2 * d.w2 12694 163 +
        energyR16 12694 * radiusPolynomialRoot16 (d.w0 12694 163) (d.w1 12694 163)
          (d.w2 12694 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12694 : ℝ) ^ 16 *
        (((458949971 / 25000000000000000000) : ℝ) + ((6530683 / 500000000000000000)) * (126 / 100) + 2 * ((119307379 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12694) *
          (32 * (((458949971 / 25000000000000000000) : ℝ) + (6530683 / 500000000000000000) + (119307379 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12694

/-! A coarse bound on the actual paper statistics constant at dimension 12695. -/
namespace BstLean.Part266.Row12695
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12693 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12693 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12693 128 ≤ (12947 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12947 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12695) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12695 : ℕ))
    (by norm_num : (12695 : ℕ) ≤ 16384)
  have ht : paperTail256 12695 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12695 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12695 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12695 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12695 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12695 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12693 128 * √(2 / (12695 : ℝ)) *
      (√(12695 : ℝ) + paperT0 12695 + paperTail256 12695) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12695 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12695 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12695 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12693 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12693 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12695 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12695

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12695
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12695 (61 / 100) 163 (17 / (100 * 12695)) (26 / (10 * 12695)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12695 (61 / 100) 163 (17 / (100 * 12695)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (477111767 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1503306101 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1283440687 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12695 / 12695 * (61 / 100)) ^ 4 * inverseRadius8 (12695 - 1) /
            envelopeGap 12695 (61 / 100) 163 (17 / (100 * 12695)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12695

namespace BstLean.Part266.Row12695
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12695 163 ≤ (2293607323 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12695 163 ≤ (9564829 / 6250000000000000)
  f2 : (tableEnvelope C).f2 ≤ (183912837 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12695 163 ≤ (183536597 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 12695 163 ≤ (1305827901 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12695 163 ≤ (477116741 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (477111767 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (477111767 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1503306101 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1283440687 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((731877 / 200000000) : ℝ) ≤ √(17 / (100 * 12695) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12695) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (87371553 / 40000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38772491551 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12695) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12695) ≤ (111399257 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12695) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12695 * (163 : ℝ) ^ 2 + 26 / (10 * 12695) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12695) : ℝ)) (tA 12695 * 163 ^ 2 + 26 / (10 * 12695)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((731877 / 200000000))) * ((477111767 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((731877 / 200000000)) ^ 3) * ((1503306101 / 1000000000000000000000000))) + ((1283440687 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((731877 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12695) : ℝ)) d.D d.V d.P (√(tA 12695) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((731877 / 200000000)) ^ 2 * (((87371553 / 40000000000000)) * ((38772491551 / 1000000000000000000)))) + ((1283440687 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12695) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((731877 / 200000000)) * ((477111767 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12695) : ℝ)) (tA 12695 * 163 ^ 2 + 26 / (10 * 12695)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((477111767 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((731877 / 200000000)) ^ 2) * ((1503306101 / 1000000000000000000000000)) + ((1283440687 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12695) : ℝ)) (√(26 / (10 * 12695) : ℝ)) d.D d.V d.P (√(tA 12695) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((731877 / 200000000)) * (((87371553 / 40000000000000)) * ((38772491551 / 1000000000000000000))) + ((1283440687 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12695) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((477111767 / 100000000000000000000) : ℝ) + ((1283440687 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12695

namespace BstLean.Part266.Row12695
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12695 163 ∧
    0 ≤ (tableEnvelope C).f1 12695 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12695 163 ∧
    0 ≤ (tableEnvelope C).w1 12695 163 ∧ 0 ≤ (tableEnvelope C).w2 12695 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12695 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12695 163 ∧ 0 ≤ d.f1 12695 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12695 163 ∧ 0 ≤ d.w1 12695 163 ∧ 0 ≤ d.w2 12695 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12695 ≤ 2 * (228 / 100 : ℝ) / 12695 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12695 ≤ 2 * (370 / 100 : ℝ) / 12695 := by
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
    (completeRAData (tableEnvelope C) 12695 163).locationBound 12695 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12695 163).energyBound 12695 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12695 163) (d.f1 12695 163) d.f2 ≤
      32 * (((2293607323 / 500000000000000000) : ℝ) + (9564829 / 6250000000000000) + (183912837 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12695 163) (d.w1 12695 163)
      (d.w2 12695 163) ≤
      32 * (((183536597 / 10000000000000000000) : ℝ) + (1305827901 / 100000000000000000000) + (477116741 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12695 163) (d.f1 12695 163) d.f2 ≤
      ((2293607323 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2293607323 / 500000000000000000)) * ((9564829 / 6250000000000000)) * (126 / 100) +
      2 * (((9564829 / 6250000000000000)) ^ 2 + 2 * ((2293607323 / 500000000000000000)) * ((183912837 / 500000000000000000))) +
      6 * ((9564829 / 6250000000000000)) * ((183912837 / 500000000000000000)) * (126 / 100) + 8 * ((183912837 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12695 163) (d.f1 12695 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12695 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12695 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12695 163) (d.f1 12695 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12695 163) (d.w1 12695 163) (d.w2 12695 163)
  have hwexpr0 : 0 ≤ d.w0 12695 163 + d.w1 12695 163 * √(π / 2) +
      2 * d.w2 12695 163 + energyR16 12695 *
      radiusPolynomialRoot16 (d.w0 12695 163) (d.w1 12695 163) (d.w2 12695 163) := by
    positivity
  constructor
  · change (12695 : ℝ) ^ 8 * (mA 12695 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12695 163) (d.f1 12695 163) d.f2 + locationR16 12695 *
        radiusPolynomialRoot16 (d.f0 12695 163) (d.f1 12695 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12695 : ℝ) ^ 8 * (mA 12695 : ℝ) ^ 8 *
        ((((2293607323 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2293607323 / 500000000000000000)) * ((9564829 / 6250000000000000)) * (126 / 100) +
          2 * (((9564829 / 6250000000000000)) ^ 2 + 2 * ((2293607323 / 500000000000000000)) * ((183912837 / 500000000000000000))) +
          6 * ((9564829 / 6250000000000000)) * ((183912837 / 500000000000000000)) * (126 / 100) + 8 * ((183912837 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12695) *
          (32 * (((2293607323 / 500000000000000000) : ℝ) + (9564829 / 6250000000000000) + (183912837 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12695 : ℝ) ^ 16 *
      (d.w0 12695 163 + d.w1 12695 163 * √(π / 2) + 2 * d.w2 12695 163 +
        energyR16 12695 * radiusPolynomialRoot16 (d.w0 12695 163) (d.w1 12695 163)
          (d.w2 12695 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12695 : ℝ) ^ 16 *
        (((183536597 / 10000000000000000000) : ℝ) + ((1305827901 / 100000000000000000000)) * (126 / 100) + 2 * ((477116741 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12695) *
          (32 * (((183536597 / 10000000000000000000) : ℝ) + (1305827901 / 100000000000000000000) + (477116741 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12695

/-! A coarse bound on the actual paper statistics constant at dimension 12696. -/
namespace BstLean.Part266.Row12696
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12694 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12694 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12694 128 ≤ (12948 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12948 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12696) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12696 : ℕ))
    (by norm_num : (12696 : ℕ) ≤ 16384)
  have ht : paperTail256 12696 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12696 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12696 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12696 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12696 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12696 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12694 128 * √(2 / (12696 : ℝ)) *
      (√(12696 : ℝ) + paperT0 12696 + paperTail256 12696) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12696 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12696 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12696 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12694 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12694 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12696 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12696

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12696
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12696 (61 / 100) 163 (17 / (100 * 12696)) (26 / (10 * 12696)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12696 (61 / 100) 163 (17 / (100 * 12696)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (476999031 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1502832507 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5130497241 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12696 / 12696 * (61 / 100)) ^ 4 * inverseRadius8 (12696 - 1) /
            envelopeGap 12696 (61 / 100) 163 (17 / (100 * 12696)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12696

namespace BstLean.Part266.Row12696
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12696 163 ≤ (4586314553 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12696 163 ≤ (765036013 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (367753333 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12696 163 ≤ (1834932947 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12696 163 ≤ (1305519663 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12696 163 ≤ (477004001 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (476999031 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (476999031 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1502832507 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5130497241 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((91481 / 25000000) : ℝ) ≤ √(17 / (100 * 12696) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12696) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2184030749 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9691595931 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12696) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12696) ≤ (111390483 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12696) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12696 * (163 : ℝ) ^ 2 + 26 / (10 * 12696) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12696) : ℝ)) (tA 12696 * 163 ^ 2 + 26 / (10 * 12696)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((91481 / 25000000))) * ((476999031 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((91481 / 25000000)) ^ 3) * ((1502832507 / 1000000000000000000000000))) + ((5130497241 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((91481 / 25000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12696) : ℝ)) d.D d.V d.P (√(tA 12696) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((91481 / 25000000)) ^ 2 * (((2184030749 / 1000000000000000)) * ((9691595931 / 250000000000000000)))) + ((5130497241 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12696) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((91481 / 25000000)) * ((476999031 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12696) : ℝ)) (tA 12696 * 163 ^ 2 + 26 / (10 * 12696)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((476999031 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((91481 / 25000000)) ^ 2) * ((1502832507 / 1000000000000000000000000)) + ((5130497241 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12696) : ℝ)) (√(26 / (10 * 12696) : ℝ)) d.D d.V d.P (√(tA 12696) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((91481 / 25000000)) * (((2184030749 / 1000000000000000)) * ((9691595931 / 250000000000000000))) + ((5130497241 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12696) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((476999031 / 100000000000000000000) : ℝ) + ((5130497241 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12696

namespace BstLean.Part266.Row12696
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12696 163 ∧
    0 ≤ (tableEnvelope C).f1 12696 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12696 163 ∧
    0 ≤ (tableEnvelope C).w1 12696 163 ∧ 0 ≤ (tableEnvelope C).w2 12696 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12696 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12696 163 ∧ 0 ≤ d.f1 12696 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12696 163 ∧ 0 ≤ d.w1 12696 163 ∧ 0 ≤ d.w2 12696 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12696 ≤ 2 * (228 / 100 : ℝ) / 12696 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12696 ≤ 2 * (370 / 100 : ℝ) / 12696 := by
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
    (completeRAData (tableEnvelope C) 12696 163).locationBound 12696 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12696 163).energyBound 12696 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12696 163) (d.f1 12696 163) d.f2 ≤
      32 * (((4586314553 / 1000000000000000000) : ℝ) + (765036013 / 500000000000000000) + (367753333 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12696 163) (d.w1 12696 163)
      (d.w2 12696 163) ≤
      32 * (((1834932947 / 100000000000000000000) : ℝ) + (1305519663 / 100000000000000000000) + (477004001 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12696 163) (d.f1 12696 163) d.f2 ≤
      ((4586314553 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4586314553 / 1000000000000000000)) * ((765036013 / 500000000000000000)) * (126 / 100) +
      2 * (((765036013 / 500000000000000000)) ^ 2 + 2 * ((4586314553 / 1000000000000000000)) * ((367753333 / 1000000000000000000))) +
      6 * ((765036013 / 500000000000000000)) * ((367753333 / 1000000000000000000)) * (126 / 100) + 8 * ((367753333 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12696 163) (d.f1 12696 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12696 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12696 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12696 163) (d.f1 12696 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12696 163) (d.w1 12696 163) (d.w2 12696 163)
  have hwexpr0 : 0 ≤ d.w0 12696 163 + d.w1 12696 163 * √(π / 2) +
      2 * d.w2 12696 163 + energyR16 12696 *
      radiusPolynomialRoot16 (d.w0 12696 163) (d.w1 12696 163) (d.w2 12696 163) := by
    positivity
  constructor
  · change (12696 : ℝ) ^ 8 * (mA 12696 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12696 163) (d.f1 12696 163) d.f2 + locationR16 12696 *
        radiusPolynomialRoot16 (d.f0 12696 163) (d.f1 12696 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12696 : ℝ) ^ 8 * (mA 12696 : ℝ) ^ 8 *
        ((((4586314553 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4586314553 / 1000000000000000000)) * ((765036013 / 500000000000000000)) * (126 / 100) +
          2 * (((765036013 / 500000000000000000)) ^ 2 + 2 * ((4586314553 / 1000000000000000000)) * ((367753333 / 1000000000000000000))) +
          6 * ((765036013 / 500000000000000000)) * ((367753333 / 1000000000000000000)) * (126 / 100) + 8 * ((367753333 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12696) *
          (32 * (((4586314553 / 1000000000000000000) : ℝ) + (765036013 / 500000000000000000) + (367753333 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12696 : ℝ) ^ 16 *
      (d.w0 12696 163 + d.w1 12696 163 * √(π / 2) + 2 * d.w2 12696 163 +
        energyR16 12696 * radiusPolynomialRoot16 (d.w0 12696 163) (d.w1 12696 163)
          (d.w2 12696 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12696 : ℝ) ^ 16 *
        (((1834932947 / 100000000000000000000) : ℝ) + ((1305519663 / 100000000000000000000)) * (126 / 100) + 2 * ((477004001 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12696) *
          (32 * (((1834932947 / 100000000000000000000) : ℝ) + (1305519663 / 100000000000000000000) + (477004001 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12696

/-! A coarse bound on the actual paper statistics constant at dimension 12697. -/
namespace BstLean.Part266.Row12697
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12695 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12695 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12695 128 ≤ (12949 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12949 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12697) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12697 : ℕ))
    (by norm_num : (12697 : ℕ) ≤ 16384)
  have ht : paperTail256 12697 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12697 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12697 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12697 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12697 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12697 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12695 128 * √(2 / (12697 : ℝ)) *
      (√(12697 : ℝ) + paperT0 12697 + paperTail256 12697) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12697 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12697 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12697 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12695 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12695 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12697 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12697

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12697
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12697 (61 / 100) 163 (17 / (100 * 12697)) (26 / (10 * 12697)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12697 (61 / 100) 163 (17 / (100 * 12697)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (47688633 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1502359099 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (640904259 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12697 / 12697 * (61 / 100)) ^ 4 * inverseRadius8 (12697 - 1) /
            envelopeGap 12697 (61 / 100) 163 (17 / (100 * 12697)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12697

namespace BstLean.Part266.Row12697
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12697 163 ≤ (4585411149 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12697 163 ≤ (1529770673 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (367680913 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12697 163 ≤ (1834499331 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12697 163 ≤ (130521117 / 10000000000000000000)
  w2 : (tableEnvelope C).w2 12697 163 ≤ (476891297 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (47688633 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (47688633 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1502359099 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (640904259 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((457387 / 125000000) : ℝ) ≤ √(17 / (100 * 12697) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12697) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1091886361 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19380138667 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12697) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12697) ≤ (11138171 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12697) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12697 * (163 : ℝ) ^ 2 + 26 / (10 * 12697) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12697) : ℝ)) (tA 12697 * 163 ^ 2 + 26 / (10 * 12697)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((457387 / 125000000))) * ((47688633 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((457387 / 125000000)) ^ 3) * ((1502359099 / 1000000000000000000000000))) + ((640904259 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((457387 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12697) : ℝ)) d.D d.V d.P (√(tA 12697) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((457387 / 125000000)) ^ 2 * (((1091886361 / 500000000000000)) * ((19380138667 / 500000000000000000)))) + ((640904259 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12697) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((457387 / 125000000)) * ((47688633 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12697) : ℝ)) (tA 12697 * 163 ^ 2 + 26 / (10 * 12697)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((47688633 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((457387 / 125000000)) ^ 2) * ((1502359099 / 1000000000000000000000000)) + ((640904259 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12697) : ℝ)) (√(26 / (10 * 12697) : ℝ)) d.D d.V d.P (√(tA 12697) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((457387 / 125000000)) * (((1091886361 / 500000000000000)) * ((19380138667 / 500000000000000000))) + ((640904259 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12697) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((47688633 / 10000000000000000000) : ℝ) + ((640904259 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12697

namespace BstLean.Part266.Row12697
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12697 163 ∧
    0 ≤ (tableEnvelope C).f1 12697 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12697 163 ∧
    0 ≤ (tableEnvelope C).w1 12697 163 ∧ 0 ≤ (tableEnvelope C).w2 12697 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12697 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12697 163 ∧ 0 ≤ d.f1 12697 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12697 163 ∧ 0 ≤ d.w1 12697 163 ∧ 0 ≤ d.w2 12697 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12697 ≤ 2 * (228 / 100 : ℝ) / 12697 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12697 ≤ 2 * (370 / 100 : ℝ) / 12697 := by
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
    (completeRAData (tableEnvelope C) 12697 163).locationBound 12697 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12697 163).energyBound 12697 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12697 163) (d.f1 12697 163) d.f2 ≤
      32 * (((4585411149 / 1000000000000000000) : ℝ) + (1529770673 / 1000000000000000000) + (367680913 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12697 163) (d.w1 12697 163)
      (d.w2 12697 163) ≤
      32 * (((1834499331 / 100000000000000000000) : ℝ) + (130521117 / 10000000000000000000) + (476891297 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12697 163) (d.f1 12697 163) d.f2 ≤
      ((4585411149 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4585411149 / 1000000000000000000)) * ((1529770673 / 1000000000000000000)) * (126 / 100) +
      2 * (((1529770673 / 1000000000000000000)) ^ 2 + 2 * ((4585411149 / 1000000000000000000)) * ((367680913 / 1000000000000000000))) +
      6 * ((1529770673 / 1000000000000000000)) * ((367680913 / 1000000000000000000)) * (126 / 100) + 8 * ((367680913 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12697 163) (d.f1 12697 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12697 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12697 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12697 163) (d.f1 12697 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12697 163) (d.w1 12697 163) (d.w2 12697 163)
  have hwexpr0 : 0 ≤ d.w0 12697 163 + d.w1 12697 163 * √(π / 2) +
      2 * d.w2 12697 163 + energyR16 12697 *
      radiusPolynomialRoot16 (d.w0 12697 163) (d.w1 12697 163) (d.w2 12697 163) := by
    positivity
  constructor
  · change (12697 : ℝ) ^ 8 * (mA 12697 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12697 163) (d.f1 12697 163) d.f2 + locationR16 12697 *
        radiusPolynomialRoot16 (d.f0 12697 163) (d.f1 12697 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12697 : ℝ) ^ 8 * (mA 12697 : ℝ) ^ 8 *
        ((((4585411149 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4585411149 / 1000000000000000000)) * ((1529770673 / 1000000000000000000)) * (126 / 100) +
          2 * (((1529770673 / 1000000000000000000)) ^ 2 + 2 * ((4585411149 / 1000000000000000000)) * ((367680913 / 1000000000000000000))) +
          6 * ((1529770673 / 1000000000000000000)) * ((367680913 / 1000000000000000000)) * (126 / 100) + 8 * ((367680913 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12697) *
          (32 * (((4585411149 / 1000000000000000000) : ℝ) + (1529770673 / 1000000000000000000) + (367680913 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12697 : ℝ) ^ 16 *
      (d.w0 12697 163 + d.w1 12697 163 * √(π / 2) + 2 * d.w2 12697 163 +
        energyR16 12697 * radiusPolynomialRoot16 (d.w0 12697 163) (d.w1 12697 163)
          (d.w2 12697 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12697 : ℝ) ^ 16 *
        (((1834499331 / 100000000000000000000) : ℝ) + ((130521117 / 10000000000000000000)) * (126 / 100) + 2 * ((476891297 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12697) *
          (32 * (((1834499331 / 100000000000000000000) : ℝ) + (130521117 / 10000000000000000000) + (476891297 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12697

/-! A coarse bound on the actual paper statistics constant at dimension 12698. -/
namespace BstLean.Part266.Row12698
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12696 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12696 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12696 128 ≤ (12950 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12950 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12698) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12698 : ℕ))
    (by norm_num : (12698 : ℕ) ≤ 16384)
  have ht : paperTail256 12698 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12698 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12698 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12698 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12698 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12698 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12696 128 * √(2 / (12698 : ℝ)) *
      (√(12698 : ℝ) + paperT0 12698 + paperTail256 12698) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12698 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12698 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12698 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12696 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12696 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12698 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12698

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12698
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12698 (61 / 100) 163 (17 / (100 * 12698)) (26 / (10 * 12698)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12698 (61 / 100) 163 (17 / (100 * 12698)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (95354733 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (750942939 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5123973241 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12698 / 12698 * (61 / 100)) ^ 4 * inverseRadius8 (12698 - 1) /
            envelopeGap 12698 (61 / 100) 163 (17 / (100 * 12698)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12698

namespace BstLean.Part266.Row12698
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12698 163 ≤ (4584508059 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12698 163 ≤ (1529469417 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (73521703 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12698 163 ≤ (366813173 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12698 163 ≤ (652451391 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12698 163 ≤ (476778629 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (95354733 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (95354733 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (750942939 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5123973241 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((457369 / 125000000) : ℝ) ≤ √(17 / (100 * 12698) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12698) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2183514747 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7750834479 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12698) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12698) ≤ (55686469 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12698) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12698 * (163 : ℝ) ^ 2 + 26 / (10 * 12698) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12698) : ℝ)) (tA 12698 * 163 ^ 2 + 26 / (10 * 12698)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((457369 / 125000000))) * ((95354733 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((457369 / 125000000)) ^ 3) * ((750942939 / 500000000000000000000000))) + ((5123973241 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((457369 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12698) : ℝ)) d.D d.V d.P (√(tA 12698) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((457369 / 125000000)) ^ 2 * (((2183514747 / 1000000000000000)) * ((7750834479 / 200000000000000000)))) + ((5123973241 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12698) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((457369 / 125000000)) * ((95354733 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12698) : ℝ)) (tA 12698 * 163 ^ 2 + 26 / (10 * 12698)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((95354733 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((457369 / 125000000)) ^ 2) * ((750942939 / 500000000000000000000000)) + ((5123973241 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12698) : ℝ)) (√(26 / (10 * 12698) : ℝ)) d.D d.V d.P (√(tA 12698) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((457369 / 125000000)) * (((2183514747 / 1000000000000000)) * ((7750834479 / 200000000000000000))) + ((5123973241 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12698) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((95354733 / 20000000000000000000) : ℝ) + ((5123973241 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12698

namespace BstLean.Part266.Row12698
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12698 163 ∧
    0 ≤ (tableEnvelope C).f1 12698 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12698 163 ∧
    0 ≤ (tableEnvelope C).w1 12698 163 ∧ 0 ≤ (tableEnvelope C).w2 12698 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12698 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12698 163 ∧ 0 ≤ d.f1 12698 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12698 163 ∧ 0 ≤ d.w1 12698 163 ∧ 0 ≤ d.w2 12698 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12698 ≤ 2 * (228 / 100 : ℝ) / 12698 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12698 ≤ 2 * (370 / 100 : ℝ) / 12698 := by
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
    (completeRAData (tableEnvelope C) 12698 163).locationBound 12698 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12698 163).energyBound 12698 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12698 163) (d.f1 12698 163) d.f2 ≤
      32 * (((4584508059 / 1000000000000000000) : ℝ) + (1529469417 / 1000000000000000000) + (73521703 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12698 163) (d.w1 12698 163)
      (d.w2 12698 163) ≤
      32 * (((366813173 / 20000000000000000000) : ℝ) + (652451391 / 50000000000000000000) + (476778629 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12698 163) (d.f1 12698 163) d.f2 ≤
      ((4584508059 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4584508059 / 1000000000000000000)) * ((1529469417 / 1000000000000000000)) * (126 / 100) +
      2 * (((1529469417 / 1000000000000000000)) ^ 2 + 2 * ((4584508059 / 1000000000000000000)) * ((73521703 / 200000000000000000))) +
      6 * ((1529469417 / 1000000000000000000)) * ((73521703 / 200000000000000000)) * (126 / 100) + 8 * ((73521703 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12698 163) (d.f1 12698 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12698 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12698 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12698 163) (d.f1 12698 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12698 163) (d.w1 12698 163) (d.w2 12698 163)
  have hwexpr0 : 0 ≤ d.w0 12698 163 + d.w1 12698 163 * √(π / 2) +
      2 * d.w2 12698 163 + energyR16 12698 *
      radiusPolynomialRoot16 (d.w0 12698 163) (d.w1 12698 163) (d.w2 12698 163) := by
    positivity
  constructor
  · change (12698 : ℝ) ^ 8 * (mA 12698 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12698 163) (d.f1 12698 163) d.f2 + locationR16 12698 *
        radiusPolynomialRoot16 (d.f0 12698 163) (d.f1 12698 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12698 : ℝ) ^ 8 * (mA 12698 : ℝ) ^ 8 *
        ((((4584508059 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4584508059 / 1000000000000000000)) * ((1529469417 / 1000000000000000000)) * (126 / 100) +
          2 * (((1529469417 / 1000000000000000000)) ^ 2 + 2 * ((4584508059 / 1000000000000000000)) * ((73521703 / 200000000000000000))) +
          6 * ((1529469417 / 1000000000000000000)) * ((73521703 / 200000000000000000)) * (126 / 100) + 8 * ((73521703 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12698) *
          (32 * (((4584508059 / 1000000000000000000) : ℝ) + (1529469417 / 1000000000000000000) + (73521703 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12698 : ℝ) ^ 16 *
      (d.w0 12698 163 + d.w1 12698 163 * √(π / 2) + 2 * d.w2 12698 163 +
        energyR16 12698 * radiusPolynomialRoot16 (d.w0 12698 163) (d.w1 12698 163)
          (d.w2 12698 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12698 : ℝ) ^ 16 *
        (((366813173 / 20000000000000000000) : ℝ) + ((652451391 / 50000000000000000000)) * (126 / 100) + 2 * ((476778629 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12698) *
          (32 * (((366813173 / 20000000000000000000) : ℝ) + (652451391 / 50000000000000000000) + (476778629 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12698

/-! A coarse bound on the actual paper statistics constant at dimension 12699. -/
namespace BstLean.Part266.Row12699
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12697 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12697 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12697 128 ≤ (12951 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12951 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12699) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12699 : ℕ))
    (by norm_num : (12699 : ℕ) ≤ 16384)
  have ht : paperTail256 12699 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12699 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12699 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12699 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12699 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12699 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12697 128 * √(2 / (12699 : ℝ)) *
      (√(12699 : ℝ) + paperT0 12699 + paperTail256 12699) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12699 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12699 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12699 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12697 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12697 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12699 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12699

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12699
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12699 (61 / 100) 163 (17 / (100 * 12699)) (26 / (10 * 12699)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12699 (61 / 100) 163 (17 / (100 * 12699)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (119165259 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1501412843 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1024142949 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12699 / 12699 * (61 / 100)) ^ 4 * inverseRadius8 (12699 - 1) /
            envelopeGap 12699 (61 / 100) 163 (17 / (100 * 12699)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12699

namespace BstLean.Part266.Row12699
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12699 163 ≤ (2291802639 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12699 163 ≤ (1529168261 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (367536139 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12699 163 ≤ (1833632549 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12699 163 ≤ (652297249 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12699 163 ≤ (476665997 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (119165259 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (119165259 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1501412843 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1024142949 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((457351 / 125000000) : ℝ) ≤ √(17 / (100 * 12699) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12699) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (87330273 / 40000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19374034447 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12699) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12699) ≤ (13920521 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12699) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12699 * (163 : ℝ) ^ 2 + 26 / (10 * 12699) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12699) : ℝ)) (tA 12699 * 163 ^ 2 + 26 / (10 * 12699)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((457351 / 125000000))) * ((119165259 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((457351 / 125000000)) ^ 3) * ((1501412843 / 1000000000000000000000000))) + ((1024142949 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((457351 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12699) : ℝ)) d.D d.V d.P (√(tA 12699) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((457351 / 125000000)) ^ 2 * (((87330273 / 40000000000000)) * ((19374034447 / 500000000000000000)))) + ((1024142949 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12699) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((457351 / 125000000)) * ((119165259 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12699) : ℝ)) (tA 12699 * 163 ^ 2 + 26 / (10 * 12699)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((119165259 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((457351 / 125000000)) ^ 2) * ((1501412843 / 1000000000000000000000000)) + ((1024142949 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12699) : ℝ)) (√(26 / (10 * 12699) : ℝ)) d.D d.V d.P (√(tA 12699) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((457351 / 125000000)) * (((87330273 / 40000000000000)) * ((19374034447 / 500000000000000000))) + ((1024142949 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12699) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((119165259 / 25000000000000000000) : ℝ) + ((1024142949 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12699

namespace BstLean.Part266.Row12699
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12699 163 ∧
    0 ≤ (tableEnvelope C).f1 12699 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12699 163 ∧
    0 ≤ (tableEnvelope C).w1 12699 163 ∧ 0 ≤ (tableEnvelope C).w2 12699 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12699 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12699 163 ∧ 0 ≤ d.f1 12699 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12699 163 ∧ 0 ≤ d.w1 12699 163 ∧ 0 ≤ d.w2 12699 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12699 ≤ 2 * (228 / 100 : ℝ) / 12699 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12699 ≤ 2 * (370 / 100 : ℝ) / 12699 := by
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
    (completeRAData (tableEnvelope C) 12699 163).locationBound 12699 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12699 163).energyBound 12699 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12699 163) (d.f1 12699 163) d.f2 ≤
      32 * (((2291802639 / 500000000000000000) : ℝ) + (1529168261 / 1000000000000000000) + (367536139 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12699 163) (d.w1 12699 163)
      (d.w2 12699 163) ≤
      32 * (((1833632549 / 100000000000000000000) : ℝ) + (652297249 / 50000000000000000000) + (476665997 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12699 163) (d.f1 12699 163) d.f2 ≤
      ((2291802639 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2291802639 / 500000000000000000)) * ((1529168261 / 1000000000000000000)) * (126 / 100) +
      2 * (((1529168261 / 1000000000000000000)) ^ 2 + 2 * ((2291802639 / 500000000000000000)) * ((367536139 / 1000000000000000000))) +
      6 * ((1529168261 / 1000000000000000000)) * ((367536139 / 1000000000000000000)) * (126 / 100) + 8 * ((367536139 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12699 163) (d.f1 12699 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12699 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12699 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12699 163) (d.f1 12699 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12699 163) (d.w1 12699 163) (d.w2 12699 163)
  have hwexpr0 : 0 ≤ d.w0 12699 163 + d.w1 12699 163 * √(π / 2) +
      2 * d.w2 12699 163 + energyR16 12699 *
      radiusPolynomialRoot16 (d.w0 12699 163) (d.w1 12699 163) (d.w2 12699 163) := by
    positivity
  constructor
  · change (12699 : ℝ) ^ 8 * (mA 12699 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12699 163) (d.f1 12699 163) d.f2 + locationR16 12699 *
        radiusPolynomialRoot16 (d.f0 12699 163) (d.f1 12699 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12699 : ℝ) ^ 8 * (mA 12699 : ℝ) ^ 8 *
        ((((2291802639 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2291802639 / 500000000000000000)) * ((1529168261 / 1000000000000000000)) * (126 / 100) +
          2 * (((1529168261 / 1000000000000000000)) ^ 2 + 2 * ((2291802639 / 500000000000000000)) * ((367536139 / 1000000000000000000))) +
          6 * ((1529168261 / 1000000000000000000)) * ((367536139 / 1000000000000000000)) * (126 / 100) + 8 * ((367536139 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12699) *
          (32 * (((2291802639 / 500000000000000000) : ℝ) + (1529168261 / 1000000000000000000) + (367536139 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12699 : ℝ) ^ 16 *
      (d.w0 12699 163 + d.w1 12699 163 * √(π / 2) + 2 * d.w2 12699 163 +
        energyR16 12699 * radiusPolynomialRoot16 (d.w0 12699 163) (d.w1 12699 163)
          (d.w2 12699 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12699 : ℝ) ^ 16 *
        (((1833632549 / 100000000000000000000) : ℝ) + ((652297249 / 50000000000000000000)) * (126 / 100) + 2 * ((476665997 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12699) *
          (32 * (((1833632549 / 100000000000000000000) : ℝ) + (652297249 / 50000000000000000000) + (476665997 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12699
