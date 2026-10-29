import BstLean.Part276Table
import BstLean.Part252TableBiasNum

/-! Numerical certificates at dimension 12224: the paper statistics constant,
the scalar envelope and the six row-polynomial coefficients. -/
namespace BstLean.Part276
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part172 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem gaussian_constant10 : gaussMomConst 128 ≤ 10 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := gaussMomConst_pow (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only at h
  rw [h]
  norm_num [Nat.factorial]

theorem radius_constant_12224 : exactRadius 12222 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12222 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12222 128 ≤ (12476 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12476 : ℝ) := by
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

theorem log_m_12224 : Real.log (mA 12224 : ℝ) ≤ 19 := by
  have hm : (0 : ℝ) < (mA 12224 : ℝ) := by norm_num [mA]
  rw [Real.log_le_iff_le_exp hm]
  have he := Real.exp_one_gt_d9
  have h19 : Real.exp 19 = Real.exp 1 ^ 19 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h19]
  have hp := pow_le_pow_left₀ (by norm_num) he.le 19
  refine le_trans ?_ hp
  norm_num [mA]

theorem paperT0_12224 : paperT0 12224 ≤ 61645 / 10000 := by
  unfold paperT0
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have := log_m_12224
  calc 2 * Real.log (mA 12224 : ℝ) ≤ 2 * 19 := by linarith
    _ ≤ _ := by norm_num

theorem statistics_constant_12224 : statisticsConstant (paperBound256 12224) ≤ 32 / 10 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12224 : ℕ))
    (by norm_num : (12224 : ℕ) ≤ 16384)
  have ht : paperTail256 12224 ≤ 10 :=
    (min_le_left _ _).trans gaussian_constant10
  have hs : √(12224 : ℝ) ≤ 11057 / 100 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12224 : ℝ)) ≤ 12792 / 1000000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12224 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12224 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12224 ≤
      (1011 / 1000 : ℝ) * (12792 / 1000000) * (11057 / 100 + 61645 / 10000 + 10) := by
    change exactRadius 12222 128 * √(2 / (12224 : ℝ)) *
      (√(12224 : ℝ) + paperT0 12224 + paperTail256 12224) ≤ _
    have hp := mul_le_mul radius_constant_12224 hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs paperT0_12224) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12224 ≤ 1 + 14143 / 10000 * 10 / 12224 := by
    have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
    have hprod := mul_le_mul h2 gaussian_constant10
      (gaussMomConst_nonneg 128) (by norm_num : (0 : ℝ) ≤ 14143 / 10000)
    unfold paperActivationFactor
    have : √2 * gaussMomConst 128 / (12224 : ℝ) ≤ 14143 / 10000 * 10 / 12224 := by
      apply div_le_div_of_nonneg_right hprod (by norm_num)
    linarith
  have hr : (30000 : ℝ) ^ ((64 : ℝ)⁻¹) ≤ 11748 / 10000 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (64 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 30000)
      (by norm_num : (64 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp
    simp only [one_div] at hp
    rw [hp]
    norm_num
  have hL0 : 0 ≤ paperLJ256 12224 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12224 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12222 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12222 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12224 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (11748 / 10000 : ℝ) *
      (((1011 / 1000 : ℝ) * (12792 / 1000000) * (11057 / 100 + 61645 / 10000 + 10)) ^ 2 *
        (1 + 14143 / 10000 * 10 / 12224 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 32 / 10 := by norm_num

theorem statistics_constant_pos_12224 : 0 < statisticsConstant (paperBound256 12224) :=
  statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12224 : ℕ))
    (by norm_num : 1 ≤ (2 : ℕ))).trans_le
      (paperStatisticsBound_le_paperBound (by norm_num) (by norm_num)))

noncomputable def sharpEnvelope (C : ℝ) : RAData :=
  envelopeData 12224 (61 / 100) 160 (17 / (100 * 12224)) (26 / (10 * 12224)) C C C

theorem sharp_envelope_gap :
    0 < envelopeGap 12224 (61 / 100) 160 (17 / (100 * 12224)) := by
  norm_num [envelopeGap, tA, mA]

theorem sharp_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 32 / 10) :
    0 ≤ (sharpEnvelope C).D ∧ (sharpEnvelope C).D ≤ 428 / 10 ^ 14 := by
  norm_num [sharpEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem sharp_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 32 / 10) :
    0 ≤ (sharpEnvelope C).V ∧ (sharpEnvelope C).V ≤ 1401 / 10 ^ 18 := by
  have hc2 : C ^ 2 ≤ 1024 / 100 := by nlinarith
  norm_num [sharpEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem sharp_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 32 / 10) :
    0 ≤ (sharpEnvelope C).P ∧ (sharpEnvelope C).P ≤ 286 / 10 ^ 17 := by
  constructor
  · dsimp [sharpEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12224 / 12224 * (61 / 100)) ^ 4 * inverseRadius8 (12224 - 1) /
            envelopeGap 12224 (61 / 100) 160 (17 / (100 * 12224)) ^ 8 * (32 / 10) ^ 4 := by
        dsimp [sharpEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]


structure SharpCoefficientCertificate (C : ℝ) : Prop where
  f0 : (sharpEnvelope C).f0 12224 160 ≤ 405 / 10 ^ 11
  f1 : (sharpEnvelope C).f1 12224 160 ≤ 135 / 10 ^ 11
  f2 : (sharpEnvelope C).f2 ≤ 325 / 10 ^ 12
  w0 : (sharpEnvelope C).w0 12224 160 ≤ 1650 / 10 ^ 14
  w1 : (sharpEnvelope C).w1 12224 160 ≤ 1175 / 10 ^ 14
  w2 : (sharpEnvelope C).w2 12224 160 ≤ 429 / 10 ^ 14

theorem sharp_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 32 / 10) :
    SharpCoefficientCertificate C := by
  let d := sharpEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ 428 / 10 ^ 14 := sharp_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ 428 / 10 ^ 14 := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ 1401 / 10 ^ 18 := sharp_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ 286 / 10 ^ 17 := sharp_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : (3729 / 1000000 : ℝ) ≤ √(17 / (100 * 12224) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12224) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2069 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 3744 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12224) * 160 ≤ 1852 / 100000 := by
    have hs : √(tA 12224) ≤ 1157 / 10 ^ 7 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12224) : ℝ) ≤ 1459 / 100000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12224 * (160 : ℝ) ^ 2 + 26 / (10 * 12224) ≤ 5554 / 10000000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12224) : ℝ)) (tA 12224 * 160 ^ 2 + 26 / (10 * 12224)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * (3729 / 1000000)) * (428 / 10 ^ 14) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * (3729 / 1000000) ^ 3) * (1401 / 10 ^ 18)) + (286 / 10 ^ 17) * (3 / 2 * (39895 / 100000) / (3729 / 1000000) * (5554 / 10000000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12224) : ℝ)) d.D d.V d.P (√(tA 12224) * 160) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / (3729 / 1000000) ^ 2 * ((2069 / 10 ^ 9) * (3744 / 10 ^ 11))) + (286 / 10 ^ 17) * (2 * (2 * (14143 / 10000) * (1852 / 100000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12224) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / (3729 / 1000000) * (428 / 10 ^ 14)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12224) : ℝ)) (tA 12224 * 160 ^ 2 + 26 / (10 * 12224)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ (428 / 10 ^ 14 : ℝ) + (24198 / 100000) / (2 * (3729 / 1000000) ^ 2) * (1401 / 10 ^ 18) + (286 / 10 ^ 17) * (4 * (5554 / 10000000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12224) : ℝ)) (√(26 / (10 * 12224) : ℝ)) d.D d.V d.P (√(tA 12224) * 160) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / (3729 / 1000000) * ((2069 / 10 ^ 9) * (3744 / 10 ^ 11)) + (286 / 10 ^ 17) * (4 * (14143 / 10000) * (1852 / 100000) * (1459 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12224) * 160) ≤ _
    unfold AW2
    calc
      _ ≤ (428 / 10 ^ 14 : ℝ) + (286 / 10 ^ 17) * (28 * (1852 / 100000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part276
