import BstLean.Part253All
import BstLean.Part277Mono

namespace BstLean.Part281.Dir12224
open Real Set MeasureTheory BstLean.Part253 BstLean.Part152 BstLean.Part209 BstLean.Part219 BstLean.Part215
open scoped ENNReal

theorem low_length_root_12224 : BstLean.Part209.lowLengthProb 12224 (1 / 100) ^ (1 / 128 : ℝ) ≤
    (1 / 1000000 : ℝ) := by
  have hp : 0 ≤ BstLean.Part209.lowLengthProb 12224 (1 / 100) := by
    unfold BstLean.Part209.lowLengthProb
    positivity
  have hexp : exp (-(12224 : ℝ) ^ 2 * (1 / 100 - 2 / (12224 : ℝ) ^ 2) ^ 2 / 4) ≤
      (1 / 2 : ℝ) ^ 3072 := by
    calc
      _ ≤ exp (3072 * (-1 : ℝ)) := exp_le_exp.mpr (by norm_num)
      _ = exp (-1 : ℝ) ^ 3072 := by simpa using exp_nat_mul (-1 : ℝ) 3072
      _ ≤ _ := pow_le_pow_left₀ (exp_pos _).le exp_minus_one_half _
  have hpow : BstLean.Part209.lowLengthProb 12224 (1 / 100) ≤
      (1 / 1000000 : ℝ) ^ 128 := by
    unfold BstLean.Part209.lowLengthProb
    calc
      _ ≤ 4 * (1 / 2 : ℝ) ^ 3072 := mul_le_mul_of_nonneg_left hexp (by norm_num)
      _ = 4 * ((1 / 2 : ℝ) ^ 24) ^ 128 := by rw [← pow_mul]
      _ ≤ (2 : ℝ) ^ 128 * ((1 / 2 : ℝ) ^ 24) ^ 128 := by
        gcongr
        norm_num
      _ = ((2 : ℝ) * (1 / 2) ^ 24) ^ 128 := by rw [mul_pow]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (by norm_num) _
  have h := root_upper (by norm_num : (128 : ℕ) ≠ 0) hp (by norm_num) hpow
  norm_num only [Nat.cast_ofNat] at h
  exact h


theorem sqrtN_upper_12224 : √(12224 : ℝ) ≤ 110.5622 := sqrt_le_iff.mpr (by norm_num)

theorem length_upper_12224 (P : ℕ) {b B : ℝ} (hb : twoGaussConst P ≤ b)
    (hnum : 2 / (12224 : ℝ) ^ 2 + 1.414213563 / 12224 * b ≤ B) :
    lengthAlpha 12224 P ≤ B := by
  unfold lengthAlpha
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hnum
  have h0 := twoGaussConst_nonneg P
  gcongr
  exact sqrt2_upper

theorem length16_upper_12224 : lengthAlpha 12224 16 ≤ 0.00043603 :=
  length_upper_12224 16 two16_upper (by norm_num)
theorem length32_upper_12224 : lengthAlpha 12224 32 ≤ 0.00059153 :=
  length_upper_12224 32 two32_upper (by norm_num)
theorem length64_upper_12224 : lengthAlpha 12224 64 ≤ 0.00081714 :=
  length_upper_12224 64 two64_upper (by norm_num)
theorem length128_upper_12224 : lengthAlpha 12224 128 ≤ 0.0011406 :=
  length_upper_12224 128 two128_upper (by norm_num)

theorem pairQ_upper_12224 : pairQ 12224 32 ≤ 0.013385 := by
  have h0 := gaussMomConst_nonneg 32
  have hs := sqrtN_upper_12224
  have hs2 := sqrt2_lower
  have hg := gauss32_upper
  unfold pairQ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 / (12224 : ℝ) ^ 2 * (110.5622 + 5.05772465) *
        (12224 / 1.414213562 + 5.05772465) := by gcongr
    _ ≤ (0.013385 : ℝ) := by norm_num

theorem pairPlane_upper_12224 : pairPlane 12224 32 ≤ 585004 := by
  have hs := sqrt32_upper
  have hl := log162_upper
  have h32 := factorial32_upper
  have h64 := factorial64_upper
  have hr : √(log (162 : ℝ) + factorialRoot 32) ≤ 4.22827381 := by
    apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · linarith
  unfold pairPlane
  simp only [Nat.cast_ofNat, Nat.reduceMul]
  calc
    _ ≤ 2 * 5.65685425 * (12224 : ℝ) * 4.22827381 +
        8 * (5.088 + 24.67407549) := by gcongr
    _ ≤ (585004 : ℝ) := by norm_num

theorem pairV_upper_12224 : pairV 12224 32 ≤ 0.021216 := by
  unfold pairV
  have hq := pairQ_upper_12224
  have hp := pairPlane_upper_12224
  simp only [Nat.cast_ofNat]
  linarith

theorem overlap_upper_12224 : overlapC 12224 16 ≤ 0.002467127 := by
  have hs := sqrt32_upper
  have h16 := overlap16_upper
  have h32 := overlap32_upper
  unfold overlapC
  simp only [Nat.cast_ofNat, Nat.reduceMul]
  rw [show (2 * (16 : ℝ)) = 32 by norm_num]
  calc
    _ ≤ 2 / (12224 : ℝ) ^ 2 *
        (5.65685425 * 12224 * 2.66487321 + 4 * 13.07036015) := by gcongr
    _ ≤ (0.002467127 : ℝ) := by norm_num

theorem delta_upper_12224 : pairDelta 12224 16 (1 / 100) ≤ 0.0034074 := by
  have ho := overlap_upper_12224
  have h16 := length16_upper_12224
  have h32 := length32_upper_12224
  have h0 := lengthAlpha_nonneg 12224 32
  unfold pairDelta
  simp only [Nat.reduceMul]
  calc
    _ ≤ ((0.002467127 : ℝ) + 2 * 0.00043603 + 0.00059153 ^ 2) / (1 - 1 / 100) ^ 2 := by
      gcongr
    _ ≤ (0.0034074 : ℝ) := by norm_num

theorem tangent_upper_12224 (P : ℕ) {b g r B : ℝ}
    (hb : twoGaussConst P ≤ b) (hg : gaussMomConst (2 * P) ≤ g)
    (hr0 : 0 ≤ r) (hr : (12224 : ℝ) ^ 2 / 2 + 12224 / 2 * b ≤ r ^ 2)
    (hnum : 2 / (12224 : ℝ) ^ 2 * (r + 110.5622 + g) ^ 2 ≤ B) :
    tangentU 12224 P ≤ B := by
  have hs : √((12224 : ℝ) ^ 2 / 2 + activeB 12224 P) ≤ r := by
    apply sqrt_le_iff.mpr
    refine ⟨hr0, ?_⟩
    unfold activeB
    simp only [Nat.cast_ofNat]
    nlinarith
  have hn := sqrtN_upper_12224
  have h0 := gaussMomConst_nonneg (2 * P)
  unfold tangentU
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hnum
  gcongr

theorem tangent32_upper_12224 : tangentU 12224 32 ≤ 1.027817 := by
  apply tangent_upper_12224 32 two32_upper gauss64_upper (r := 8645.48076)
    <;> norm_num

theorem tangent64_upper_12224 : tangentU 12224 64 ≤ 1.028638 := by
  apply tangent_upper_12224 64 two64_upper gauss128_upper (r := 8646.17007)
    <;> norm_num

theorem error_epsilon_upper_12224 : pairEpsilon 12224 16 (1 / 100) ≤ 0.0647 := by
  have hV := pairV_upper_12224
  have hQ := pairQ_upper_12224
  have hQ0 := pairQ_nonneg 12224 32
  have hV0 := pairV_nonneg 12224 32
  have hd : √(pairDelta 12224 16 (1 / 100)) ≤ 0.058373 :=
    sqrt_le_iff.mpr ⟨by norm_num, delta_upper_12224.trans (by norm_num)⟩
  have ht32 : √(tangentU 12224 32) ≤ 1.0138131 :=
    sqrt_le_iff.mpr ⟨by norm_num, tangent32_upper_12224.trans (by norm_num)⟩
  have ht64 : √(tangentU 12224 64) ≤ 1.014218 :=
    sqrt_le_iff.mpr ⟨by norm_num, tangent64_upper_12224.trans (by norm_num)⟩
  have hl64 := length64_upper_12224
  have hl128 := length128_upper_12224
  have hl0 := lengthAlpha_nonneg 12224 128
  have hrad : radialCoefficient (1 / 100) ≤ 0.324741 := by
    unfold radialCoefficient
    apply (div_le_iff₀ (by positivity : 0 < π * (1 - 1 / 100))).mpr
    linarith [pi_gt_d6]
  have hr0 := radialCoefficient_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 100)
    (by norm_num : (1 / 100 : ℝ) < 1)
  have hlow := low_length_root_12224
  have hlow0 : 0 ≤ lowLengthProb 12224 (1 / 100) ^ (1 / 128 : ℝ) :=
    rpow_nonneg (by unfold lowLengthProb; positivity) _
  have hcomp : complementB 12224 16 (1 / 100) ≤
      (1.014218 * (1 + 0.0011406) + 1) * (1 / 1000000 : ℝ) := by
    unfold complementB complementRoot
    simp only [Nat.reduceMul, Nat.cast_ofNat]
    rw [show (8 * (16 : ℝ)) = 128 by norm_num]
    gcongr
  have hfluc : fluctuationRoot 12224 16 ≤
      (0.021216 : ℝ) * 1.0138131 * (1 + 0.00081714) := by
    have hl640 := lengthAlpha_nonneg 12224 64
    have hprod := mul_le_mul hV ht32 (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 0.021216)
    have hh := mul_le_mul hprod (add_le_add (le_refl (1 : ℝ)) hl64)
      (by linarith : (0 : ℝ) ≤ 1 + lengthAlpha 12224 64) (by norm_num)
    simpa only [fluctuationRoot, Nat.reduceMul] using hh
  have hmean : meanEpsilon 12224 16 (1 / 100) ≤
      0.021216 + (3 / 10 : ℝ) * 0.058373 + 0.324741 * 0.013385 +
        (1.014218 * (1 + 0.0011406) + 1) * (1 / 1000000) := by
    have hh := add_le_add (add_le_add (add_le_add hV
      (mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 3 / 10)))
      (mul_le_mul hrad hQ hQ0 (by norm_num : (0 : ℝ) ≤ 0.324741))) hcomp
    simpa only [meanEpsilon, Nat.reduceMul] using hh
  unfold pairEpsilon
  linarith


theorem radius_upper_12224 {θ b R : ℝ} (j : ℕ) (hθ : 0 ≤ θ) (hb : θ ≤ b)
    (hd : 0 < 1 - (2 * j + 2 : ℝ) * b / 12224)
    (hR : b / (1 - (2 * j + 2 : ℝ) * b / 12224) ≤ R) :
    radiusCoefficient 12224 j θ ≤ R := by
  unfold radiusCoefficient
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hR
  apply div_le_div₀ (hθ.trans hb) hb hd
  have hj : (0 : ℝ) ≤ 2 * j + 2 := by positivity
  nlinarith

theorem amplitude_upper_12224 {θ a b A : ℝ} (ha : a ≤ θ) (hb : θ ≤ b) (hb1 : b ≤ 1)
    (hd : 0 < 1 - 4 * b / 12224) (hA0 : 0 ≤ A)
    (hA : (1 - a) / (1 - 4 * b / 12224) ≤ A ^ 2) :
    paperAmplitude 12224 θ ≤ A := by
  unfold paperAmplitude
  apply sqrt_le_iff.mpr
  refine ⟨hA0, ?_⟩
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hA
  apply div_le_div₀ (by linarith : 0 ≤ 1 - a) (by linarith) hd
  linarith

/-- The remaining premises are rational bounds on the radius and slope terms. -/
theorem ideal_from_bounds_12224 {θ e A K R1 R4 R24 R48 R96 T : ℝ}
    (hθ : 0 ≤ θ) (he : 0.665 ≤ e) (hT : θ ≤ T) (hT0 : 0 ≤ T) (hT1 : T ≤ 0.54)
    (hA0 : 0 ≤ A) (hK0 : 0 ≤ K)
    (hA : paperAmplitude 12224 θ ≤ A) (hK : BstLean.Part219.kernelSlope (1 - θ) ≤ K)
    (h1 : radiusCoefficient 12224 1 θ ≤ R1)
    (h4 : radiusCoefficient 12224 4 θ ≤ R4)
    (h24 : radiusCoefficient 12224 24 θ ≤ R24)
    (h48 : radiusCoefficient 12224 48 θ ≤ R48)
    (h96 : radiusCoefficient 12224 96 θ ≤ R96)
    (hR1 : 0 ≤ R1) (hR4 : 0 ≤ R4) (hR24 : 0 ≤ R24)
    (hR48 : 0 ≤ R48) (hR96 : 0 ≤ R96)
    (hscalar : K * A * R48 * 1.001921 / 0.815475 +
      (77 / 100 : ℝ) * √R24 / 0.815475 *
        (√(R1 / 12224) + A * 6.7 * R96 * 1.003879 / 110.562199 +
          2 * ((T + √T * R4 * 1.000123) / 12224)) ≤ 0.2289) :
    paperIdeal 12224 θ e ≤ 0.2289 := by
  have hsE : (0.815475 : ℝ) ≤ √e := le_sqrt_of_sq_le (by linarith)
  have hsN : (110.562199 : ℝ) ≤ √12224 := le_sqrt_of_sq_le (by norm_num)
  have h47 : √(1 + 47 / (12224 : ℝ)) ≤ 1.001921 := sqrt_le_iff.mpr (by norm_num)
  have h95 : √(1 + 95 / (12224 : ℝ)) ≤ 1.003879 := sqrt_le_iff.mpr (by norm_num)
  have h3 : √(1 + 3 / (12224 : ℝ)) ≤ 1.000123 := sqrt_le_iff.mpr (by norm_num)
  have hr := rotation24_upper
  have hrad (j : ℕ) (hj : j ≤ 96) : 0 ≤ radiusCoefficient 12224 j θ := by
    unfold radiusCoefficient
    have hjR : (j : ℝ) ≤ 96 := by exact_mod_cast hj
    have hjc : (2 * j + 2 : ℝ) ≤ 194 := by linarith
    have hp := mul_le_mul hjc (hT.trans hT1) hθ (by norm_num : (0 : ℝ) ≤ 194)
    apply div_nonneg hθ
    simp only [Nat.cast_ofNat]
    nlinarith
  have hr1 := hrad 1 (by norm_num)
  have hr4 := hrad 4 (by norm_num)
  have hr24 := hrad 24 (by norm_num)
  have hr48 := hrad 48 (by norm_num)
  have hr96 := hrad 96 (by norm_num)
  have hslope := BstLean.Part219.kernelSlope_nonneg (1 - θ)
  have hAmp : 0 ≤ paperAmplitude 12224 θ := by unfold paperAmplitude; positivity
  have hrot := BstLean.Part195.rotationConstant_nonneg 24
  unfold paperIdeal paperBias
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hscalar
  gcongr


theorem idealCell0_12224 {θ e : ℝ} (hw : θ ∈ Icc (0.47199 : ℝ) 0.4744)
    (he : 0.665 ≤ e) : paperIdeal 12224 θ e ≤ 0.2289 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 12224 θ ≤ 0.72669938 :=
    amplitude_upper_12224 hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : BstLean.Part219.kernelSlope (1 - θ) ≤ 0.48526907 := by
    apply BstLean.Part253.slope_upper (Q := (0.52801 : ℝ)) (K := (0.62790227 : ℝ)) (s := (0.84923816 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 12224 1 θ ≤ 0.47447366 :=
    radius_upper_12224 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 12224 4 θ ≤ 0.47458419 :=
    radius_upper_12224 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 12224 24 θ ≤ 0.47532234 :=
    radius_upper_12224 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 12224 48 θ ≤ 0.47621117 :=
    radius_upper_12224 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 12224 96 θ ≤ 0.47799882 :=
    radius_upper_12224 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds_12224 hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.47532234 : ℝ) ≤ 0.68943625 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.47447366 : ℝ) / 12224) ≤ 0.00623017 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.4744 : ℝ) ≤ 0.68876702 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.48526907 : ℝ) * 0.72669938 * 0.47621117 * 1.001921 / 0.815475 +
        (77 / 100) * 0.68943625 / 0.815475 *
          (0.00623017 + 0.72669938 * 6.7 * 0.47799882 * 1.003879 / 110.562199 +
            2 * ((0.4744 + 0.68876702 * 0.47458419 * 1.000123) / 12224)) := by gcongr
    _ ≤ (0.2289 : ℝ) := by norm_num

theorem idealCell1_12224 {θ e : ℝ} (hw : θ ∈ Icc (0.4744 : ℝ) 0.4816)
    (he : 0.665 ≤ e) : paperIdeal 12224 θ e ≤ 0.2289 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 12224 θ ≤ 0.72503990 :=
    amplitude_upper_12224 hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : BstLean.Part219.kernelSlope (1 - θ) ≤ 0.48416285 := by
    apply BstLean.Part253.slope_upper (Q := (0.5256 : ℝ)) (K := (0.62626878 : ℝ)) (s := (0.85073183 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 12224 1 θ ≤ 0.48167591 :=
    radius_upper_12224 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 12224 4 θ ≤ 0.48178982 :=
    radius_upper_12224 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 12224 24 θ ≤ 0.48255058 :=
    radius_upper_12224 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 12224 48 θ ≤ 0.48346667 :=
    radius_upper_12224 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 12224 96 θ ≤ 0.48530932 :=
    radius_upper_12224 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds_12224 hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.48255058 : ℝ) ≤ 0.69465861 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.48167591 : ℝ) / 12224) ≤ 0.00627727 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.4816 : ℝ) ≤ 0.69397407 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.48416285 : ℝ) * 0.72503990 * 0.48346667 * 1.001921 / 0.815475 +
        (77 / 100) * 0.69465861 / 0.815475 *
          (0.00627727 + 0.72503990 * 6.7 * 0.48530932 * 1.003879 / 110.562199 +
            2 * ((0.4816 + 0.69397407 * 0.48178982 * 1.000123) / 12224)) := by gcongr
    _ ≤ (0.2289 : ℝ) := by norm_num

theorem idealCell2_12224 {θ e : ℝ} (hw : θ ∈ Icc (0.4816 : ℝ) 0.4888)
    (he : 0.665 ≤ e) : paperIdeal 12224 θ e ≤ 0.2289 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 12224 θ ≤ 0.72005759 :=
    amplitude_upper_12224 hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : BstLean.Part219.kernelSlope (1 - θ) ≤ 0.48088081 := by
    apply BstLean.Part253.slope_upper (Q := (0.5184 : ℝ)) (K := (0.62140204 : ℝ)) (s := (0.85513826 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 12224 1 θ ≤ 0.48887820 :=
    radius_upper_12224 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 12224 4 θ ≤ 0.48899554 :=
    radius_upper_12224 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 12224 24 θ ≤ 0.48977924 :=
    radius_upper_12224 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 12224 48 θ ≤ 0.49072301 :=
    radius_upper_12224 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 12224 96 θ ≤ 0.49262150 :=
    radius_upper_12224 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds_12224 hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.48977924 : ℝ) ≤ 0.69984230 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.48887820 : ℝ) / 12224) ≤ 0.00632403 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.4888 : ℝ) ≤ 0.69914234 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.48088081 : ℝ) * 0.72005759 * 0.49072301 * 1.001921 / 0.815475 +
        (77 / 100) * 0.69984230 / 0.815475 *
          (0.00632403 + 0.72005759 * 6.7 * 0.49262150 * 1.003879 / 110.562199 +
            2 * ((0.4888 + 0.69914234 * 0.48899554 * 1.000123) / 12224)) := by gcongr
    _ ≤ (0.2289 : ℝ) := by norm_num

theorem idealCell3_12224 {θ e : ℝ} (hw : θ ∈ Icc (0.4888 : ℝ) 0.496)
    (he : 0.665 ≤ e) : paperIdeal 12224 θ e ≤ 0.2289 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 12224 θ ≤ 0.71504055 :=
    amplitude_upper_12224 hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : BstLean.Part219.kernelSlope (1 - θ) ≤ 0.47763237 := by
    apply BstLean.Part253.slope_upper (Q := (0.5112 : ℝ)) (K := (0.61655526 : ℝ)) (s := (0.85946179 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 12224 1 θ ≤ 0.49608052 :=
    radius_upper_12224 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 12224 4 θ ≤ 0.49620134 :=
    radius_upper_12224 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 12224 24 θ ≤ 0.49700833 :=
    radius_upper_12224 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 12224 48 θ ≤ 0.49798019 :=
    radius_upper_12224 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 12224 96 θ ≤ 0.49993536 :=
    radius_upper_12224 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds_12224 hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.49700833 : ℝ) ≤ 0.70498818 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.49608052 : ℝ) / 12224) ≤ 0.00637044 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.496 : ℝ) ≤ 0.70427268 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.47763237 : ℝ) * 0.71504055 * 0.49798019 * 1.001921 / 0.815475 +
        (77 / 100) * 0.70498818 / 0.815475 *
          (0.00637044 + 0.71504055 * 6.7 * 0.49993536 * 1.003879 / 110.562199 +
            2 * ((0.496 + 0.70427268 * 0.49620134 * 1.000123) / 12224)) := by gcongr
    _ ≤ (0.2289 : ℝ) := by norm_num

theorem idealCell4_12224 {θ e : ℝ} (hw : θ ∈ Icc (0.496 : ℝ) 0.5032)
    (he : 0.665 ≤ e) : paperIdeal 12224 θ e ≤ 0.2289 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 12224 θ ≤ 0.70998803 :=
    amplitude_upper_12224 hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : BstLean.Part219.kernelSlope (1 - θ) ≤ 0.47441674 := by
    apply BstLean.Part253.slope_upper (Q := (0.504 : ℝ)) (K := (0.61172830 : ℝ)) (s := (0.86370366 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 12224 1 θ ≤ 0.50328288 :=
    radius_upper_12224 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 12224 4 θ ≤ 0.50340723 :=
    radius_upper_12224 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 12224 24 θ ≤ 0.50423785 :=
    radius_upper_12224 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 12224 48 θ ≤ 0.50523822 :=
    radius_upper_12224 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 12224 96 θ ≤ 0.50725091 :=
    radius_upper_12224 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds_12224 hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.50423785 : ℝ) ≤ 0.71009708 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.50328288 : ℝ) / 12224) ≤ 0.00641652 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.5032 : ℝ) ≤ 0.70936592 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.47441674 : ℝ) * 0.70998803 * 0.50523822 * 1.001921 / 0.815475 +
        (77 / 100) * 0.71009708 / 0.815475 *
          (0.00641652 + 0.70998803 * 6.7 * 0.50725091 * 1.003879 / 110.562199 +
            2 * ((0.5032 + 0.70936592 * 0.50340723 * 1.000123) / 12224)) := by gcongr
    _ ≤ (0.2289 : ℝ) := by norm_num

theorem idealCell5_12224 {θ e : ℝ} (hw : θ ∈ Icc (0.5032 : ℝ) 0.5104)
    (he : 0.665 ≤ e) : paperIdeal 12224 θ e ≤ 0.2289 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 12224 θ ≤ 0.70489928 :=
    amplitude_upper_12224 hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : BstLean.Part219.kernelSlope (1 - θ) ≤ 0.47123312 := by
    apply BstLean.Part253.slope_upper (Q := (0.4968 : ℝ)) (K := (0.60692102 : ℝ)) (s := (0.86786506 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 12224 1 θ ≤ 0.51048526 :=
    radius_upper_12224 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 12224 4 θ ≤ 0.51061321 :=
    radius_upper_12224 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 12224 24 θ ≤ 0.51146779 :=
    radius_upper_12224 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 12224 48 θ ≤ 0.51249708 :=
    radius_upper_12224 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 12224 96 θ ≤ 0.51456814 :=
    radius_upper_12224 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds_12224 hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.51146779 : ℝ) ≤ 0.71516977 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.51048526 : ℝ) / 12224) ≤ 0.00646227 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.5104 : ℝ) ≤ 0.71442285 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.47123312 : ℝ) * 0.70489928 * 0.51249708 * 1.001921 / 0.815475 +
        (77 / 100) * 0.71516977 / 0.815475 *
          (0.00646227 + 0.70489928 * 6.7 * 0.51456814 * 1.003879 / 110.562199 +
            2 * ((0.5104 + 0.71442285 * 0.51061321 * 1.000123) / 12224)) := by gcongr
    _ ≤ (0.2289 : ℝ) := by norm_num

theorem idealCell6_12224 {θ e : ℝ} (hw : θ ∈ Icc (0.5104 : ℝ) 0.5176)
    (he : 0.665 ≤ e) : paperIdeal 12224 θ e ≤ 0.2289 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 12224 θ ≤ 0.69977350 :=
    amplitude_upper_12224 hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : BstLean.Part219.kernelSlope (1 - θ) ≤ 0.46808077 := by
    apply BstLean.Part253.slope_upper (Q := (0.4896 : ℝ)) (K := (0.60213330 : ℝ)) (s := (0.87194716 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 12224 1 θ ≤ 0.51768769 :=
    radius_upper_12224 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 12224 4 θ ≤ 0.51781926 :=
    radius_upper_12224 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 12224 24 θ ≤ 0.51869817 :=
    radius_upper_12224 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 12224 48 θ ≤ 0.51975679 :=
    radius_upper_12224 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 12224 96 θ ≤ 0.52188706 :=
    radius_upper_12224 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds_12224 hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.51869817 : ℝ) ≤ 0.72020704 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.51768769 : ℝ) / 12224) ≤ 0.00650770 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.5176 : ℝ) ≤ 0.71944423 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.46808077 : ℝ) * 0.69977350 * 0.51975679 * 1.001921 / 0.815475 +
        (77 / 100) * 0.72020704 / 0.815475 *
          (0.00650770 + 0.69977350 * 6.7 * 0.52188706 * 1.003879 / 110.562199 +
            2 * ((0.5176 + 0.71944423 * 0.51781926 * 1.000123) / 12224)) := by gcongr
    _ ≤ (0.2289 : ℝ) := by norm_num

theorem idealCell7_12224 {θ e : ℝ} (hw : θ ∈ Icc (0.5176 : ℝ) 0.52358)
    (he : 0.665 ≤ e) : paperIdeal 12224 θ e ≤ 0.2289 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 12224 θ ≤ 0.69460972 :=
    amplitude_upper_12224 hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : BstLean.Part219.kernelSlope (1 - θ) ≤ 0.46495896 := by
    apply BstLean.Part253.slope_upper (Q := (0.4824 : ℝ)) (K := (0.59736500 : ℝ)) (s := (0.87595105 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 12224 1 θ ≤ 0.52366972 :=
    radius_upper_12224 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 12224 4 θ ≤ 0.52380436 :=
    radius_upper_12224 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 12224 24 θ ≤ 0.52470371 :=
    radius_upper_12224 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 12224 48 θ ≤ 0.52578702 :=
    radius_upper_12224 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 12224 96 θ ≤ 0.52796711 :=
    radius_upper_12224 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds_12224 hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.52470371 : ℝ) ≤ 0.72436435 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.52366972 : ℝ) / 12224) ≤ 0.00654519 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.52358 : ℝ) ≤ 0.72358829 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.46495896 : ℝ) * 0.69460972 * 0.52578702 * 1.001921 / 0.815475 +
        (77 / 100) * 0.72436435 / 0.815475 *
          (0.00654519 + 0.69460972 * 6.7 * 0.52796711 * 1.003879 / 110.562199 +
            2 * ((0.52358 + 0.72358829 * 0.52380436 * 1.000123) / 12224)) := by gcongr
    _ ≤ (0.2289 : ℝ) := by norm_num

theorem ideal_window_12224 {θ e : ℝ} (hw : θ ∈ Icc (0.47199 : ℝ) 0.52358)
    (he : 0.665 ≤ e) : paperIdeal 12224 θ e ≤ 0.2289 := by
  by_cases h1 : θ ≤ 0.4744
  · exact idealCell0_12224 ⟨hw.1, h1⟩ he
  by_cases h2 : θ ≤ 0.4816
  · exact idealCell1_12224 ⟨by linarith, h2⟩ he
  by_cases h3 : θ ≤ 0.4888
  · exact idealCell2_12224 ⟨by linarith, h3⟩ he
  by_cases h4 : θ ≤ 0.496
  · exact idealCell3_12224 ⟨by linarith, h4⟩ he
  by_cases h5 : θ ≤ 0.5032
  · exact idealCell4_12224 ⟨by linarith, h5⟩ he
  by_cases h6 : θ ≤ 0.5104
  · exact idealCell5_12224 ⟨by linarith, h6⟩ he
  by_cases h7 : θ ≤ 0.5176
  · exact idealCell6_12224 ⟨by linarith, h7⟩ he
  exact idealCell7_12224 ⟨by linarith, hw.2⟩ he


theorem direction_budget_12224 {n : ℕ} (hn : 12224 ≤ n)
    (c : Fin n → ℝ) (τ e xi eta : ℝ) (δ : ℝ≥0∞)
    (hw : BstLean.Part150.thetaC c τ ∈ Icc (0.47199 : ℝ) 0.52358)
    (he : 0.665 ≤ e) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.1)
    (hop : operatorAllowance c τ eta δ ^ 2 ≤ 1.25) :
    paperDirectionBudget c τ e xi eta δ ≤ (0.08892 : ℝ) := by
  have hroot : (0.88 : ℝ) ≤ (7 / 25000 : ℝ) ^ (1 / 64 : ℝ) := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (64 : ℕ) ≠ 0) (by positivity)
    have hh := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 7 / 25000)
      (by norm_num : (64 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hh
    rw [hh]
    norm_num
  have h := BstLean.Part277.direction_budget_leP (n0 := 12224) (by norm_num) hn c τ e xi eta δ
    (θlo := 0.47199) (θhi := 0.52358) (e0 := 0.665) (xi0 := 0.1) (MP := 1.25)
    (I0 := 0.2289) (ε0 := 0.0647) (Rc := 0.525) (sR := 0.889) (ρ0 := 0.88)
    (by norm_num) hw (by norm_num) (by norm_num) he hxi hxi1 hop (by norm_num)
    (fun θ hθ e' he' => ideal_window_12224 hθ (by linarith))
    (fun θ hθ => radius_upper_12224 12 (le_trans (by norm_num) hθ.1) hθ.2
      (by norm_num) (by norm_num))
    error_epsilon_upper_12224 (by norm_num) (by norm_num) (by norm_num) hroot
  refine h.trans ?_
  have hs : √((1.25 : ℝ) * 0.1 / ((12224 : ℕ) * 0.665)) ≤ 0.00393 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    norm_num
  calc _ ≤ ((0.2289 : ℝ) + 0.0647 * 0.889 / 0.88 + 0.00393) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part281.Dir12224

namespace BstLean.Part281.Dir12000
open Real Set MeasureTheory BstLean.Part253 BstLean.Part152 BstLean.Part209 BstLean.Part219 BstLean.Part215
open scoped ENNReal

theorem low_length_root_12000 : BstLean.Part209.lowLengthProb 12000 (1 / 100) ^ (1 / 128 : ℝ) ≤
    (1 / 1000000 : ℝ) := by
  have hp : 0 ≤ BstLean.Part209.lowLengthProb 12000 (1 / 100) := by
    unfold BstLean.Part209.lowLengthProb
    positivity
  have hexp : exp (-(12000 : ℝ) ^ 2 * (1 / 100 - 2 / (12000 : ℝ) ^ 2) ^ 2 / 4) ≤
      (1 / 2 : ℝ) ^ 3072 := by
    calc
      _ ≤ exp (3072 * (-1 : ℝ)) := exp_le_exp.mpr (by norm_num)
      _ = exp (-1 : ℝ) ^ 3072 := by simpa using exp_nat_mul (-1 : ℝ) 3072
      _ ≤ _ := pow_le_pow_left₀ (exp_pos _).le exp_minus_one_half _
  have hpow : BstLean.Part209.lowLengthProb 12000 (1 / 100) ≤
      (1 / 1000000 : ℝ) ^ 128 := by
    unfold BstLean.Part209.lowLengthProb
    calc
      _ ≤ 4 * (1 / 2 : ℝ) ^ 3072 := mul_le_mul_of_nonneg_left hexp (by norm_num)
      _ = 4 * ((1 / 2 : ℝ) ^ 24) ^ 128 := by rw [← pow_mul]
      _ ≤ (2 : ℝ) ^ 128 * ((1 / 2 : ℝ) ^ 24) ^ 128 := by
        gcongr
        norm_num
      _ = ((2 : ℝ) * (1 / 2) ^ 24) ^ 128 := by rw [mul_pow]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (by norm_num) _
  have h := root_upper (by norm_num : (128 : ℕ) ≠ 0) hp (by norm_num) hpow
  norm_num only [Nat.cast_ofNat] at h
  exact h


theorem sqrtN_upper_12000 : √(12000 : ℝ) ≤ 109.544512 := sqrt_le_iff.mpr (by norm_num)

theorem length_upper_12000 (P : ℕ) {b B : ℝ} (hb : twoGaussConst P ≤ b)
    (hnum : 2 / (12000 : ℝ) ^ 2 + 1.414213563 / 12000 * b ≤ B) :
    lengthAlpha 12000 P ≤ B := by
  unfold lengthAlpha
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hnum
  have h0 := twoGaussConst_nonneg P
  gcongr
  exact sqrt2_upper

theorem length16_upper_12000 : lengthAlpha 12000 16 ≤ 0.00044416 :=
  length_upper_12000 16 two16_upper (by norm_num)
theorem length32_upper_12000 : lengthAlpha 12000 32 ≤ 0.00060257 :=
  length_upper_12000 32 two32_upper (by norm_num)
theorem length64_upper_12000 : lengthAlpha 12000 64 ≤ 0.0008324 :=
  length_upper_12000 64 two64_upper (by norm_num)
theorem length128_upper_12000 : lengthAlpha 12000 128 ≤ 0.00116189 :=
  length_upper_12000 128 two128_upper (by norm_num)

theorem pairQ_upper_12000 : pairQ 12000 32 ≤ 0.013515 := by
  have h0 := gaussMomConst_nonneg 32
  have hs := sqrtN_upper_12000
  have hs2 := sqrt2_lower
  have hg := gauss32_upper
  unfold pairQ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 / (12000 : ℝ) ^ 2 * (109.544512 + 5.05772465) *
        (12000 / 1.414213562 + 5.05772465) := by gcongr
    _ ≤ (0.013515 : ℝ) := by norm_num

theorem pairPlane_upper_12000 : pairPlane 12000 32 ≤ 574288 := by
  have hs := sqrt32_upper
  have hl := log162_upper
  have h32 := factorial32_upper
  have h64 := factorial64_upper
  have hr : √(log (162 : ℝ) + factorialRoot 32) ≤ 4.22827381 := by
    apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · linarith
  unfold pairPlane
  simp only [Nat.cast_ofNat, Nat.reduceMul]
  calc
    _ ≤ 2 * 5.65685425 * (12000 : ℝ) * 4.22827381 +
        8 * (5.088 + 24.67407549) := by gcongr
    _ ≤ (574288 : ℝ) := by norm_num

theorem pairV_upper_12000 : pairV 12000 32 ≤ 0.021492 := by
  unfold pairV
  have hq := pairQ_upper_12000
  have hp := pairPlane_upper_12000
  simp only [Nat.cast_ofNat]
  linarith

theorem overlap_upper_12000 : overlapC 12000 16 ≤ 0.002513193 := by
  have hs := sqrt32_upper
  have h16 := overlap16_upper
  have h32 := overlap32_upper
  unfold overlapC
  simp only [Nat.cast_ofNat, Nat.reduceMul]
  rw [show (2 * (16 : ℝ)) = 32 by norm_num]
  calc
    _ ≤ 2 / (12000 : ℝ) ^ 2 *
        (5.65685425 * 12000 * 2.66487321 + 4 * 13.07036015) := by gcongr
    _ ≤ (0.002513193 : ℝ) := by norm_num

theorem delta_upper_12000 : pairDelta 12000 16 (1 / 100) ≤ 0.003471 := by
  have ho := overlap_upper_12000
  have h16 := length16_upper_12000
  have h32 := length32_upper_12000
  have h0 := lengthAlpha_nonneg 12000 32
  unfold pairDelta
  simp only [Nat.reduceMul]
  calc
    _ ≤ ((0.002513193 : ℝ) + 2 * 0.00044416 + 0.00060257 ^ 2) / (1 - 1 / 100) ^ 2 := by
      gcongr
    _ ≤ (0.003471 : ℝ) := by norm_num

theorem tangent_upper_12000 (P : ℕ) {b g r B : ℝ}
    (hb : twoGaussConst P ≤ b) (hg : gaussMomConst (2 * P) ≤ g)
    (hr0 : 0 ≤ r) (hr : (12000 : ℝ) ^ 2 / 2 + 12000 / 2 * b ≤ r ^ 2)
    (hnum : 2 / (12000 : ℝ) ^ 2 * (r + 109.544512 + g) ^ 2 ≤ B) :
    tangentU 12000 P ≤ B := by
  have hs : √((12000 : ℝ) ^ 2 / 2 + activeB 12000 P) ≤ r := by
    apply sqrt_le_iff.mpr
    refine ⟨hr0, ?_⟩
    unfold activeB
    simp only [Nat.cast_ofNat]
    nlinarith
  have hn := sqrtN_upper_12000
  have h0 := gaussMomConst_nonneg (2 * P)
  unfold tangentU
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hnum
  gcongr

theorem tangent32_upper_12000 : tangentU 12000 32 ≤ 1.028097 := by
  apply tangent_upper_12000 32 two32_upper gauss64_upper (r := 8487.08883)
    <;> norm_num

theorem tangent64_upper_12000 : tangentU 12000 64 ≤ 1.028933 := by
  apply tangent_upper_12000 64 two64_upper gauss128_upper (r := 8487.77815)
    <;> norm_num

theorem error_epsilon_upper_12000 : pairEpsilon 12000 16 (1 / 100) ≤ 0.0654 := by
  have hV := pairV_upper_12000
  have hQ := pairQ_upper_12000
  have hQ0 := pairQ_nonneg 12000 32
  have hV0 := pairV_nonneg 12000 32
  have hd : √(pairDelta 12000 16 (1 / 100)) ≤ 0.058916 :=
    sqrt_le_iff.mpr ⟨by norm_num, delta_upper_12000.trans (by norm_num)⟩
  have ht32 : √(tangentU 12000 32) ≤ 1.0139512 :=
    sqrt_le_iff.mpr ⟨by norm_num, tangent32_upper_12000.trans (by norm_num)⟩
  have ht64 : √(tangentU 12000 64) ≤ 1.0143634 :=
    sqrt_le_iff.mpr ⟨by norm_num, tangent64_upper_12000.trans (by norm_num)⟩
  have hl64 := length64_upper_12000
  have hl128 := length128_upper_12000
  have hl0 := lengthAlpha_nonneg 12000 128
  have hrad : radialCoefficient (1 / 100) ≤ 0.324741 := by
    unfold radialCoefficient
    apply (div_le_iff₀ (by positivity : 0 < π * (1 - 1 / 100))).mpr
    linarith [pi_gt_d6]
  have hr0 := radialCoefficient_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 100)
    (by norm_num : (1 / 100 : ℝ) < 1)
  have hlow := low_length_root_12000
  have hlow0 : 0 ≤ lowLengthProb 12000 (1 / 100) ^ (1 / 128 : ℝ) :=
    rpow_nonneg (by unfold lowLengthProb; positivity) _
  have hcomp : complementB 12000 16 (1 / 100) ≤
      (1.0143634 * (1 + 0.00116189) + 1) * (1 / 1000000 : ℝ) := by
    unfold complementB complementRoot
    simp only [Nat.reduceMul, Nat.cast_ofNat]
    rw [show (8 * (16 : ℝ)) = 128 by norm_num]
    gcongr
  have hfluc : fluctuationRoot 12000 16 ≤
      (0.021492 : ℝ) * 1.0139512 * (1 + 0.0008324) := by
    have hl640 := lengthAlpha_nonneg 12000 64
    have hprod := mul_le_mul hV ht32 (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 0.021492)
    have hh := mul_le_mul hprod (add_le_add (le_refl (1 : ℝ)) hl64)
      (by linarith : (0 : ℝ) ≤ 1 + lengthAlpha 12000 64) (by norm_num)
    simpa only [fluctuationRoot, Nat.reduceMul] using hh
  have hmean : meanEpsilon 12000 16 (1 / 100) ≤
      0.021492 + (3 / 10 : ℝ) * 0.058916 + 0.324741 * 0.013515 +
        (1.0143634 * (1 + 0.00116189) + 1) * (1 / 1000000) := by
    have hh := add_le_add (add_le_add (add_le_add hV
      (mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 3 / 10)))
      (mul_le_mul hrad hQ hQ0 (by norm_num : (0 : ℝ) ≤ 0.324741))) hcomp
    simpa only [meanEpsilon, Nat.reduceMul] using hh
  unfold pairEpsilon
  linarith


theorem radius_upper_12000 {θ b R : ℝ} (j : ℕ) (hθ : 0 ≤ θ) (hb : θ ≤ b)
    (hd : 0 < 1 - (2 * j + 2 : ℝ) * b / 12000)
    (hR : b / (1 - (2 * j + 2 : ℝ) * b / 12000) ≤ R) :
    radiusCoefficient 12000 j θ ≤ R := by
  unfold radiusCoefficient
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hR
  apply div_le_div₀ (hθ.trans hb) hb hd
  have hj : (0 : ℝ) ≤ 2 * j + 2 := by positivity
  nlinarith

theorem amplitude_upper_12000 {θ a b A : ℝ} (ha : a ≤ θ) (hb : θ ≤ b) (hb1 : b ≤ 1)
    (hd : 0 < 1 - 4 * b / 12000) (hA0 : 0 ≤ A)
    (hA : (1 - a) / (1 - 4 * b / 12000) ≤ A ^ 2) :
    paperAmplitude 12000 θ ≤ A := by
  unfold paperAmplitude
  apply sqrt_le_iff.mpr
  refine ⟨hA0, ?_⟩
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hA
  apply div_le_div₀ (by linarith : 0 ≤ 1 - a) (by linarith) hd
  linarith

/-- The remaining premises are rational bounds on the radius and slope terms. -/
theorem ideal_from_bounds_12000 {θ e A K R1 R4 R24 R48 R96 T : ℝ}
    (hθ : 0 ≤ θ) (he : 0.665 ≤ e) (hT : θ ≤ T) (hT0 : 0 ≤ T) (hT1 : T ≤ 0.54)
    (hA0 : 0 ≤ A) (hK0 : 0 ≤ K)
    (hA : paperAmplitude 12000 θ ≤ A) (hK : BstLean.Part219.kernelSlope (1 - θ) ≤ K)
    (h1 : radiusCoefficient 12000 1 θ ≤ R1)
    (h4 : radiusCoefficient 12000 4 θ ≤ R4)
    (h24 : radiusCoefficient 12000 24 θ ≤ R24)
    (h48 : radiusCoefficient 12000 48 θ ≤ R48)
    (h96 : radiusCoefficient 12000 96 θ ≤ R96)
    (hR1 : 0 ≤ R1) (hR4 : 0 ≤ R4) (hR24 : 0 ≤ R24)
    (hR48 : 0 ≤ R48) (hR96 : 0 ≤ R96)
    (hscalar : K * A * R48 * 1.001957 / 0.815475 +
      (77 / 100 : ℝ) * √R24 / 0.815475 *
        (√(R1 / 12000) + A * 6.7 * R96 * 1.003951 / 109.544511 +
          2 * ((T + √T * R4 * 1.000125) / 12000)) ≤ 0.2291) :
    paperIdeal 12000 θ e ≤ 0.2291 := by
  have hsE : (0.815475 : ℝ) ≤ √e := le_sqrt_of_sq_le (by linarith)
  have hsN : (109.544511 : ℝ) ≤ √12000 := le_sqrt_of_sq_le (by norm_num)
  have h47 : √(1 + 47 / (12000 : ℝ)) ≤ 1.001957 := sqrt_le_iff.mpr (by norm_num)
  have h95 : √(1 + 95 / (12000 : ℝ)) ≤ 1.003951 := sqrt_le_iff.mpr (by norm_num)
  have h3 : √(1 + 3 / (12000 : ℝ)) ≤ 1.000125 := sqrt_le_iff.mpr (by norm_num)
  have hr := rotation24_upper
  have hrad (j : ℕ) (hj : j ≤ 96) : 0 ≤ radiusCoefficient 12000 j θ := by
    unfold radiusCoefficient
    have hjR : (j : ℝ) ≤ 96 := by exact_mod_cast hj
    have hjc : (2 * j + 2 : ℝ) ≤ 194 := by linarith
    have hp := mul_le_mul hjc (hT.trans hT1) hθ (by norm_num : (0 : ℝ) ≤ 194)
    apply div_nonneg hθ
    simp only [Nat.cast_ofNat]
    nlinarith
  have hr1 := hrad 1 (by norm_num)
  have hr4 := hrad 4 (by norm_num)
  have hr24 := hrad 24 (by norm_num)
  have hr48 := hrad 48 (by norm_num)
  have hr96 := hrad 96 (by norm_num)
  have hslope := BstLean.Part219.kernelSlope_nonneg (1 - θ)
  have hAmp : 0 ≤ paperAmplitude 12000 θ := by unfold paperAmplitude; positivity
  have hrot := BstLean.Part195.rotationConstant_nonneg 24
  unfold paperIdeal paperBias
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hscalar
  gcongr


theorem idealCell0_12000 {θ e : ℝ} (hw : θ ∈ Icc (0.47199 : ℝ) 0.4744)
    (he : 0.665 ≤ e) : paperIdeal 12000 θ e ≤ 0.2291 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 12000 θ ≤ 0.72670043 :=
    amplitude_upper_12000 hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : BstLean.Part219.kernelSlope (1 - θ) ≤ 0.48526907 := by
    apply BstLean.Part253.slope_upper (Q := (0.52801 : ℝ)) (K := (0.62790227 : ℝ)) (s := (0.84923816 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 12000 1 θ ≤ 0.47447504 :=
    radius_upper_12000 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 12000 4 θ ≤ 0.47458763 :=
    radius_upper_12000 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 12000 24 θ ≤ 0.47533959 :=
    radius_upper_12000 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 12000 48 θ ≤ 0.47624511 :=
    radius_upper_12000 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 12000 96 θ ≤ 0.47806652 :=
    radius_upper_12000 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds_12000 hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.47533959 : ℝ) ≤ 0.68944876 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.47447504 : ℝ) / 12000) ≤ 0.00628806 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.4744 : ℝ) ≤ 0.68876702 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.48526907 : ℝ) * 0.72670043 * 0.47624511 * 1.001957 / 0.815475 +
        (77 / 100) * 0.68944876 / 0.815475 *
          (0.00628806 + 0.72670043 * 6.7 * 0.47806652 * 1.003951 / 109.544511 +
            2 * ((0.4744 + 0.68876702 * 0.47458763 * 1.000125) / 12000)) := by gcongr
    _ ≤ (0.2291 : ℝ) := by norm_num

theorem idealCell1_12000 {θ e : ℝ} (hw : θ ∈ Icc (0.4744 : ℝ) 0.4816)
    (he : 0.665 ≤ e) : paperIdeal 12000 θ e ≤ 0.2291 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 12000 θ ≤ 0.72504096 :=
    amplitude_upper_12000 hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : BstLean.Part219.kernelSlope (1 - θ) ≤ 0.48416285 := by
    apply BstLean.Part253.slope_upper (Q := (0.5256 : ℝ)) (K := (0.62626878 : ℝ)) (s := (0.85073183 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 12000 1 θ ≤ 0.48167733 :=
    radius_upper_12000 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 12000 4 θ ≤ 0.48179336 :=
    radius_upper_12000 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 12000 24 θ ≤ 0.48256836 :=
    radius_upper_12000 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 12000 48 θ ≤ 0.48350165 :=
    radius_upper_12000 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 12000 96 θ ≤ 0.48537910 :=
    radius_upper_12000 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds_12000 hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.48256836 : ℝ) ≤ 0.69467141 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.48167733 : ℝ) / 12000) ≤ 0.00633560 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.4816 : ℝ) ≤ 0.69397407 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.48416285 : ℝ) * 0.72504096 * 0.48350165 * 1.001957 / 0.815475 +
        (77 / 100) * 0.69467141 / 0.815475 *
          (0.00633560 + 0.72504096 * 6.7 * 0.48537910 * 1.003951 / 109.544511 +
            2 * ((0.4816 + 0.69397407 * 0.48179336 * 1.000125) / 12000)) := by gcongr
    _ ≤ (0.2291 : ℝ) := by norm_num

theorem idealCell2_12000 {θ e : ℝ} (hw : θ ∈ Icc (0.4816 : ℝ) 0.4888)
    (he : 0.665 ≤ e) : paperIdeal 12000 θ e ≤ 0.2291 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 12000 θ ≤ 0.72005867 :=
    amplitude_upper_12000 hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : BstLean.Part219.kernelSlope (1 - θ) ≤ 0.48088081 := by
    apply BstLean.Part253.slope_upper (Q := (0.5184 : ℝ)) (K := (0.62140204 : ℝ)) (s := (0.85513826 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 12000 1 θ ≤ 0.48887966 :=
    radius_upper_12000 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 12000 4 θ ≤ 0.48899919 :=
    radius_upper_12000 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 12000 24 θ ≤ 0.48979756 :=
    radius_upper_12000 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 12000 48 θ ≤ 0.49075905 :=
    radius_upper_12000 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 12000 96 θ ≤ 0.49269340 :=
    radius_upper_12000 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds_12000 hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.48979756 : ℝ) ≤ 0.69985539 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.48887966 : ℝ) / 12000) ≤ 0.00638279 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.4888 : ℝ) ≤ 0.69914234 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.48088081 : ℝ) * 0.72005867 * 0.49075905 * 1.001957 / 0.815475 +
        (77 / 100) * 0.69985539 / 0.815475 *
          (0.00638279 + 0.72005867 * 6.7 * 0.49269340 * 1.003951 / 109.544511 +
            2 * ((0.4888 + 0.69914234 * 0.48899919 * 1.000125) / 12000)) := by gcongr
    _ ≤ (0.2291 : ℝ) := by norm_num

theorem idealCell3_12000 {θ e : ℝ} (hw : θ ∈ Icc (0.4888 : ℝ) 0.496)
    (he : 0.665 ≤ e) : paperIdeal 12000 θ e ≤ 0.2291 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 12000 θ ≤ 0.71504163 :=
    amplitude_upper_12000 hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : BstLean.Part219.kernelSlope (1 - θ) ≤ 0.47763237 := by
    apply BstLean.Part253.slope_upper (Q := (0.5112 : ℝ)) (K := (0.61655526 : ℝ)) (s := (0.85946179 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 12000 1 θ ≤ 0.49608202 :=
    radius_upper_12000 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 12000 4 θ ≤ 0.49620510 :=
    radius_upper_12000 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 12000 24 θ ≤ 0.49702719 :=
    radius_upper_12000 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 12000 48 θ ≤ 0.49801731 :=
    radius_upper_12000 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 12000 96 θ ≤ 0.50000941 :=
    radius_upper_12000 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds_12000 hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.49702719 : ℝ) ≤ 0.70500156 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.49608202 : ℝ) / 12000) ≤ 0.00642964 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.496 : ℝ) ≤ 0.70427268 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.47763237 : ℝ) * 0.71504163 * 0.49801731 * 1.001957 / 0.815475 +
        (77 / 100) * 0.70500156 / 0.815475 *
          (0.00642964 + 0.71504163 * 6.7 * 0.50000941 * 1.003951 / 109.544511 +
            2 * ((0.496 + 0.70427268 * 0.49620510 * 1.000125) / 12000)) := by gcongr
    _ ≤ (0.2291 : ℝ) := by norm_num

theorem idealCell4_12000 {θ e : ℝ} (hw : θ ∈ Icc (0.496 : ℝ) 0.5032)
    (he : 0.665 ≤ e) : paperIdeal 12000 θ e ≤ 0.2291 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 12000 θ ≤ 0.70998913 :=
    amplitude_upper_12000 hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : BstLean.Part219.kernelSlope (1 - θ) ≤ 0.47441674 := by
    apply BstLean.Part253.slope_upper (Q := (0.504 : ℝ)) (K := (0.61172830 : ℝ)) (s := (0.86370366 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 12000 1 θ ≤ 0.50328442 :=
    radius_upper_12000 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 12000 4 θ ≤ 0.50341110 :=
    radius_upper_12000 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 12000 24 θ ≤ 0.50425726 :=
    radius_upper_12000 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 12000 48 θ ≤ 0.50527642 :=
    radius_upper_12000 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 12000 96 θ ≤ 0.50732715 :=
    radius_upper_12000 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds_12000 hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.50425726 : ℝ) ≤ 0.71011074 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.50328442 : ℝ) / 12000) ≤ 0.00647614 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.5032 : ℝ) ≤ 0.70936592 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.47441674 : ℝ) * 0.70998913 * 0.50527642 * 1.001957 / 0.815475 +
        (77 / 100) * 0.71011074 / 0.815475 *
          (0.00647614 + 0.70998913 * 6.7 * 0.50732715 * 1.003951 / 109.544511 +
            2 * ((0.5032 + 0.70936592 * 0.50341110 * 1.000125) / 12000)) := by gcongr
    _ ≤ (0.2291 : ℝ) := by norm_num

theorem idealCell5_12000 {θ e : ℝ} (hw : θ ∈ Icc (0.5032 : ℝ) 0.5104)
    (he : 0.665 ≤ e) : paperIdeal 12000 θ e ≤ 0.2291 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 12000 θ ≤ 0.70490038 :=
    amplitude_upper_12000 hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : BstLean.Part219.kernelSlope (1 - θ) ≤ 0.47123312 := by
    apply BstLean.Part253.slope_upper (Q := (0.4968 : ℝ)) (K := (0.60692102 : ℝ)) (s := (0.86786506 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 12000 1 θ ≤ 0.51048686 :=
    radius_upper_12000 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 12000 4 θ ≤ 0.51061719 :=
    radius_upper_12000 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 12000 24 θ ≤ 0.51148777 :=
    radius_upper_12000 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 12000 48 θ ≤ 0.51253639 :=
    radius_upper_12000 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 12000 96 θ ≤ 0.51464659 :=
    radius_upper_12000 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds_12000 hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.51148777 : ℝ) ≤ 0.71518374 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.51048686 : ℝ) / 12000) ≤ 0.00652232 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.5104 : ℝ) ≤ 0.71442285 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.47123312 : ℝ) * 0.70490038 * 0.51253639 * 1.001957 / 0.815475 +
        (77 / 100) * 0.71518374 / 0.815475 *
          (0.00652232 + 0.70490038 * 6.7 * 0.51464659 * 1.003951 / 109.544511 +
            2 * ((0.5104 + 0.71442285 * 0.51061719 * 1.000125) / 12000)) := by gcongr
    _ ≤ (0.2291 : ℝ) := by norm_num

theorem idealCell6_12000 {θ e : ℝ} (hw : θ ∈ Icc (0.5104 : ℝ) 0.5176)
    (he : 0.665 ≤ e) : paperIdeal 12000 θ e ≤ 0.2291 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 12000 θ ≤ 0.69977460 :=
    amplitude_upper_12000 hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : BstLean.Part219.kernelSlope (1 - θ) ≤ 0.46808077 := by
    apply BstLean.Part253.slope_upper (Q := (0.4896 : ℝ)) (K := (0.60213330 : ℝ)) (s := (0.87194716 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 12000 1 θ ≤ 0.51768932 :=
    radius_upper_12000 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 12000 4 θ ≤ 0.51782336 :=
    radius_upper_12000 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 12000 24 θ ≤ 0.51871871 :=
    radius_upper_12000 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 12000 48 θ ≤ 0.51979722 :=
    radius_upper_12000 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 12000 96 θ ≤ 0.52196776 :=
    radius_upper_12000 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds_12000 hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.51871871 : ℝ) ≤ 0.72022130 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.51768932 : ℝ) / 12000) ≤ 0.00656817 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.5176 : ℝ) ≤ 0.71944423 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.46808077 : ℝ) * 0.69977460 * 0.51979722 * 1.001957 / 0.815475 +
        (77 / 100) * 0.72022130 / 0.815475 *
          (0.00656817 + 0.69977460 * 6.7 * 0.52196776 * 1.003951 / 109.544511 +
            2 * ((0.5176 + 0.71944423 * 0.51782336 * 1.000125) / 12000)) := by gcongr
    _ ≤ (0.2291 : ℝ) := by norm_num

theorem idealCell7_12000 {θ e : ℝ} (hw : θ ∈ Icc (0.5176 : ℝ) 0.52358)
    (he : 0.665 ≤ e) : paperIdeal 12000 θ e ≤ 0.2291 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 12000 θ ≤ 0.69461084 :=
    amplitude_upper_12000 hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : BstLean.Part219.kernelSlope (1 - θ) ≤ 0.46495896 := by
    apply BstLean.Part253.slope_upper (Q := (0.4824 : ℝ)) (K := (0.59736500 : ℝ)) (s := (0.87595105 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 12000 1 θ ≤ 0.52367140 :=
    radius_upper_12000 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 12000 4 θ ≤ 0.52380855 :=
    radius_upper_12000 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 12000 24 θ ≤ 0.52472474 :=
    radius_upper_12000 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 12000 48 θ ≤ 0.52582840 :=
    radius_upper_12000 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 12000 96 θ ≤ 0.52804970 :=
    radius_upper_12000 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds_12000 hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.52472474 : ℝ) ≤ 0.72437887 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.52367140 : ℝ) / 12000) ≤ 0.00660601 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.52358 : ℝ) ≤ 0.72358829 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.46495896 : ℝ) * 0.69461084 * 0.52582840 * 1.001957 / 0.815475 +
        (77 / 100) * 0.72437887 / 0.815475 *
          (0.00660601 + 0.69461084 * 6.7 * 0.52804970 * 1.003951 / 109.544511 +
            2 * ((0.52358 + 0.72358829 * 0.52380855 * 1.000125) / 12000)) := by gcongr
    _ ≤ (0.2291 : ℝ) := by norm_num

theorem ideal_window_12000 {θ e : ℝ} (hw : θ ∈ Icc (0.47199 : ℝ) 0.52358)
    (he : 0.665 ≤ e) : paperIdeal 12000 θ e ≤ 0.2291 := by
  by_cases h1 : θ ≤ 0.4744
  · exact idealCell0_12000 ⟨hw.1, h1⟩ he
  by_cases h2 : θ ≤ 0.4816
  · exact idealCell1_12000 ⟨by linarith, h2⟩ he
  by_cases h3 : θ ≤ 0.4888
  · exact idealCell2_12000 ⟨by linarith, h3⟩ he
  by_cases h4 : θ ≤ 0.496
  · exact idealCell3_12000 ⟨by linarith, h4⟩ he
  by_cases h5 : θ ≤ 0.5032
  · exact idealCell4_12000 ⟨by linarith, h5⟩ he
  by_cases h6 : θ ≤ 0.5104
  · exact idealCell5_12000 ⟨by linarith, h6⟩ he
  by_cases h7 : θ ≤ 0.5176
  · exact idealCell6_12000 ⟨by linarith, h7⟩ he
  exact idealCell7_12000 ⟨by linarith, hw.2⟩ he


theorem direction_budget_12000 {n : ℕ} (hn : 12000 ≤ n)
    (c : Fin n → ℝ) (τ e xi eta : ℝ) (δ : ℝ≥0∞)
    (hw : BstLean.Part150.thetaC c τ ∈ Icc (0.47199 : ℝ) 0.52358)
    (he : 0.665 ≤ e) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.1)
    (hop : operatorAllowance c τ eta δ ^ 2 ≤ 1.25) :
    paperDirectionBudget c τ e xi eta δ ≤ (0.08948 : ℝ) := by
  have hroot : (0.88 : ℝ) ≤ (7 / 25000 : ℝ) ^ (1 / 64 : ℝ) := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (64 : ℕ) ≠ 0) (by positivity)
    have hh := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 7 / 25000)
      (by norm_num : (64 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hh
    rw [hh]
    norm_num
  have h := BstLean.Part277.direction_budget_leP (n0 := 12000) (by norm_num) hn c τ e xi eta δ
    (θlo := 0.47199) (θhi := 0.52358) (e0 := 0.665) (xi0 := 0.1) (MP := 1.25)
    (I0 := 0.2291) (ε0 := 0.0654) (Rc := 0.525) (sR := 0.889) (ρ0 := 0.88)
    (by norm_num) hw (by norm_num) (by norm_num) he hxi hxi1 hop (by norm_num)
    (fun θ hθ e' he' => ideal_window_12000 hθ (by linarith))
    (fun θ hθ => radius_upper_12000 12 (le_trans (by norm_num) hθ.1) hθ.2
      (by norm_num) (by norm_num))
    error_epsilon_upper_12000 (by norm_num) (by norm_num) (by norm_num) hroot
  refine h.trans ?_
  have hs : √((1.25 : ℝ) * 0.1 / ((12000 : ℕ) * 0.665)) ≤ 0.00396 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    norm_num
  calc _ ≤ ((0.2291 : ℝ) + 0.0654 * 0.889 / 0.88 + 0.00396) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part281.Dir12000

namespace BstLean.Part281.Dir11883
open Real Set MeasureTheory BstLean.Part253 BstLean.Part152 BstLean.Part209 BstLean.Part219 BstLean.Part215
open scoped ENNReal

theorem low_length_root_11883 : BstLean.Part209.lowLengthProb 11883 (1 / 100) ^ (1 / 128 : ℝ) ≤
    (1 / 1000000 : ℝ) := by
  have hp : 0 ≤ BstLean.Part209.lowLengthProb 11883 (1 / 100) := by
    unfold BstLean.Part209.lowLengthProb
    positivity
  have hexp : exp (-(11883 : ℝ) ^ 2 * (1 / 100 - 2 / (11883 : ℝ) ^ 2) ^ 2 / 4) ≤
      (1 / 2 : ℝ) ^ 3072 := by
    calc
      _ ≤ exp (3072 * (-1 : ℝ)) := exp_le_exp.mpr (by norm_num)
      _ = exp (-1 : ℝ) ^ 3072 := by simpa using exp_nat_mul (-1 : ℝ) 3072
      _ ≤ _ := pow_le_pow_left₀ (exp_pos _).le exp_minus_one_half _
  have hpow : BstLean.Part209.lowLengthProb 11883 (1 / 100) ≤
      (1 / 1000000 : ℝ) ^ 128 := by
    unfold BstLean.Part209.lowLengthProb
    calc
      _ ≤ 4 * (1 / 2 : ℝ) ^ 3072 := mul_le_mul_of_nonneg_left hexp (by norm_num)
      _ = 4 * ((1 / 2 : ℝ) ^ 24) ^ 128 := by rw [← pow_mul]
      _ ≤ (2 : ℝ) ^ 128 * ((1 / 2 : ℝ) ^ 24) ^ 128 := by
        gcongr
        norm_num
      _ = ((2 : ℝ) * (1 / 2) ^ 24) ^ 128 := by rw [mul_pow]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (by norm_num) _
  have h := root_upper (by norm_num : (128 : ℕ) ≠ 0) hp (by norm_num) hpow
  norm_num only [Nat.cast_ofNat] at h
  exact h


theorem sqrtN_upper_11883 : √(11883 : ℝ) ≤ 109.009174 := sqrt_le_iff.mpr (by norm_num)

theorem length_upper_11883 (P : ℕ) {b B : ℝ} (hb : twoGaussConst P ≤ b)
    (hnum : 2 / (11883 : ℝ) ^ 2 + 1.414213563 / 11883 * b ≤ B) :
    lengthAlpha 11883 P ≤ B := by
  unfold lengthAlpha
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hnum
  have h0 := twoGaussConst_nonneg P
  gcongr
  exact sqrt2_upper

theorem length16_upper_11883 : lengthAlpha 11883 16 ≤ 0.00044854 :=
  length_upper_11883 16 two16_upper (by norm_num)
theorem length32_upper_11883 : lengthAlpha 11883 32 ≤ 0.0006085 :=
  length_upper_11883 32 two32_upper (by norm_num)
theorem length64_upper_11883 : lengthAlpha 11883 64 ≤ 0.00084059 :=
  length_upper_11883 64 two64_upper (by norm_num)
theorem length128_upper_11883 : lengthAlpha 11883 128 ≤ 0.00117333 :=
  length_upper_11883 128 two128_upper (by norm_num)

theorem pairQ_upper_11883 : pairQ 11883 32 ≤ 0.013584 := by
  have h0 := gaussMomConst_nonneg 32
  have hs := sqrtN_upper_11883
  have hs2 := sqrt2_lower
  have hg := gauss32_upper
  unfold pairQ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 / (11883 : ℝ) ^ 2 * (109.009174 + 5.05772465) *
        (11883 / 1.414213562 + 5.05772465) := by gcongr
    _ ≤ (0.013584 : ℝ) := by norm_num

theorem pairPlane_upper_11883 : pairPlane 11883 32 ≤ 568691 := by
  have hs := sqrt32_upper
  have hl := log162_upper
  have h32 := factorial32_upper
  have h64 := factorial64_upper
  have hr : √(log (162 : ℝ) + factorialRoot 32) ≤ 4.22827381 := by
    apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · linarith
  unfold pairPlane
  simp only [Nat.cast_ofNat, Nat.reduceMul]
  calc
    _ ≤ 2 * 5.65685425 * (11883 : ℝ) * 4.22827381 +
        8 * (5.088 + 24.67407549) := by gcongr
    _ ≤ (568691 : ℝ) := by norm_num

theorem pairV_upper_11883 : pairV 11883 32 ≤ 0.021639 := by
  unfold pairV
  have hq := pairQ_upper_11883
  have hp := pairPlane_upper_11883
  simp only [Nat.cast_ofNat]
  linarith

theorem overlap_upper_11883 : overlapC 11883 16 ≤ 0.002537945 := by
  have hs := sqrt32_upper
  have h16 := overlap16_upper
  have h32 := overlap32_upper
  unfold overlapC
  simp only [Nat.cast_ofNat, Nat.reduceMul]
  rw [show (2 * (16 : ℝ)) = 32 by norm_num]
  calc
    _ ≤ 2 / (11883 : ℝ) ^ 2 *
        (5.65685425 * 11883 * 2.66487321 + 4 * 13.07036015) := by gcongr
    _ ≤ (0.002537945 : ℝ) := by norm_num

theorem delta_upper_11883 : pairDelta 11883 16 (1 / 100) ≤ 0.0035052 := by
  have ho := overlap_upper_11883
  have h16 := length16_upper_11883
  have h32 := length32_upper_11883
  have h0 := lengthAlpha_nonneg 11883 32
  unfold pairDelta
  simp only [Nat.reduceMul]
  calc
    _ ≤ ((0.002537945 : ℝ) + 2 * 0.00044854 + 0.0006085 ^ 2) / (1 - 1 / 100) ^ 2 := by
      gcongr
    _ ≤ (0.0035052 : ℝ) := by norm_num

theorem tangent_upper_11883 (P : ℕ) {b g r B : ℝ}
    (hb : twoGaussConst P ≤ b) (hg : gaussMomConst (2 * P) ≤ g)
    (hr0 : 0 ≤ r) (hr : (11883 : ℝ) ^ 2 / 2 + 11883 / 2 * b ≤ r ^ 2)
    (hnum : 2 / (11883 : ℝ) ^ 2 * (r + 109.009174 + g) ^ 2 ≤ B) :
    tangentU 11883 P ≤ B := by
  have hs : √((11883 : ℝ) ^ 2 / 2 + activeB 11883 P) ≤ r := by
    apply sqrt_le_iff.mpr
    refine ⟨hr0, ?_⟩
    unfold activeB
    simp only [Nat.cast_ofNat]
    nlinarith
  have hn := sqrtN_upper_11883
  have h0 := gaussMomConst_nonneg (2 * P)
  unfold tangentU
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hnum
  gcongr

theorem tangent32_upper_11883 : tangentU 11883 32 ≤ 1.028246 := by
  apply tangent_upper_11883 32 two32_upper gauss64_upper (r := 8404.35734)
    <;> norm_num

theorem tangent64_upper_11883 : tangentU 11883 64 ≤ 1.02909 := by
  apply tangent_upper_11883 64 two64_upper gauss128_upper (r := 8405.04665)
    <;> norm_num

theorem error_epsilon_upper_11883 : pairEpsilon 11883 16 (1 / 100) ≤ 0.0658 := by
  have hV := pairV_upper_11883
  have hQ := pairQ_upper_11883
  have hQ0 := pairQ_nonneg 11883 32
  have hV0 := pairV_nonneg 11883 32
  have hd : √(pairDelta 11883 16 (1 / 100)) ≤ 0.059205 :=
    sqrt_le_iff.mpr ⟨by norm_num, delta_upper_11883.trans (by norm_num)⟩
  have ht32 : √(tangentU 11883 32) ≤ 1.0140247 :=
    sqrt_le_iff.mpr ⟨by norm_num, tangent32_upper_11883.trans (by norm_num)⟩
  have ht64 : √(tangentU 11883 64) ≤ 1.0144408 :=
    sqrt_le_iff.mpr ⟨by norm_num, tangent64_upper_11883.trans (by norm_num)⟩
  have hl64 := length64_upper_11883
  have hl128 := length128_upper_11883
  have hl0 := lengthAlpha_nonneg 11883 128
  have hrad : radialCoefficient (1 / 100) ≤ 0.324741 := by
    unfold radialCoefficient
    apply (div_le_iff₀ (by positivity : 0 < π * (1 - 1 / 100))).mpr
    linarith [pi_gt_d6]
  have hr0 := radialCoefficient_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 100)
    (by norm_num : (1 / 100 : ℝ) < 1)
  have hlow := low_length_root_11883
  have hlow0 : 0 ≤ lowLengthProb 11883 (1 / 100) ^ (1 / 128 : ℝ) :=
    rpow_nonneg (by unfold lowLengthProb; positivity) _
  have hcomp : complementB 11883 16 (1 / 100) ≤
      (1.0144408 * (1 + 0.00117333) + 1) * (1 / 1000000 : ℝ) := by
    unfold complementB complementRoot
    simp only [Nat.reduceMul, Nat.cast_ofNat]
    rw [show (8 * (16 : ℝ)) = 128 by norm_num]
    gcongr
  have hfluc : fluctuationRoot 11883 16 ≤
      (0.021639 : ℝ) * 1.0140247 * (1 + 0.00084059) := by
    have hl640 := lengthAlpha_nonneg 11883 64
    have hprod := mul_le_mul hV ht32 (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 0.021639)
    have hh := mul_le_mul hprod (add_le_add (le_refl (1 : ℝ)) hl64)
      (by linarith : (0 : ℝ) ≤ 1 + lengthAlpha 11883 64) (by norm_num)
    simpa only [fluctuationRoot, Nat.reduceMul] using hh
  have hmean : meanEpsilon 11883 16 (1 / 100) ≤
      0.021639 + (3 / 10 : ℝ) * 0.059205 + 0.324741 * 0.013584 +
        (1.0144408 * (1 + 0.00117333) + 1) * (1 / 1000000) := by
    have hh := add_le_add (add_le_add (add_le_add hV
      (mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 3 / 10)))
      (mul_le_mul hrad hQ hQ0 (by norm_num : (0 : ℝ) ≤ 0.324741))) hcomp
    simpa only [meanEpsilon, Nat.reduceMul] using hh
  unfold pairEpsilon
  linarith


theorem radius_upper_11883 {θ b R : ℝ} (j : ℕ) (hθ : 0 ≤ θ) (hb : θ ≤ b)
    (hd : 0 < 1 - (2 * j + 2 : ℝ) * b / 11883)
    (hR : b / (1 - (2 * j + 2 : ℝ) * b / 11883) ≤ R) :
    radiusCoefficient 11883 j θ ≤ R := by
  unfold radiusCoefficient
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hR
  apply div_le_div₀ (hθ.trans hb) hb hd
  have hj : (0 : ℝ) ≤ 2 * j + 2 := by positivity
  nlinarith

theorem amplitude_upper_11883 {θ a b A : ℝ} (ha : a ≤ θ) (hb : θ ≤ b) (hb1 : b ≤ 1)
    (hd : 0 < 1 - 4 * b / 11883) (hA0 : 0 ≤ A)
    (hA : (1 - a) / (1 - 4 * b / 11883) ≤ A ^ 2) :
    paperAmplitude 11883 θ ≤ A := by
  unfold paperAmplitude
  apply sqrt_le_iff.mpr
  refine ⟨hA0, ?_⟩
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hA
  apply div_le_div₀ (by linarith : 0 ≤ 1 - a) (by linarith) hd
  linarith

/-- The remaining premises are rational bounds on the radius and slope terms. -/
theorem ideal_from_bounds_11883 {θ e A K R1 R4 R24 R48 R96 T : ℝ}
    (hθ : 0 ≤ θ) (he : 0.665 ≤ e) (hT : θ ≤ T) (hT0 : 0 ≤ T) (hT1 : T ≤ 0.54)
    (hA0 : 0 ≤ A) (hK0 : 0 ≤ K)
    (hA : paperAmplitude 11883 θ ≤ A) (hK : BstLean.Part219.kernelSlope (1 - θ) ≤ K)
    (h1 : radiusCoefficient 11883 1 θ ≤ R1)
    (h4 : radiusCoefficient 11883 4 θ ≤ R4)
    (h24 : radiusCoefficient 11883 24 θ ≤ R24)
    (h48 : radiusCoefficient 11883 48 θ ≤ R48)
    (h96 : radiusCoefficient 11883 96 θ ≤ R96)
    (hR1 : 0 ≤ R1) (hR4 : 0 ≤ R4) (hR24 : 0 ≤ R24)
    (hR48 : 0 ≤ R48) (hR96 : 0 ≤ R96)
    (hscalar : K * A * R48 * 1.001976 / 0.815475 +
      (77 / 100 : ℝ) * √R24 / 0.815475 *
        (√(R1 / 11883) + A * 6.7 * R96 * 1.00399 / 109.009173 +
          2 * ((T + √T * R4 * 1.000127) / 11883)) ≤ 0.2292) :
    paperIdeal 11883 θ e ≤ 0.2292 := by
  have hsE : (0.815475 : ℝ) ≤ √e := le_sqrt_of_sq_le (by linarith)
  have hsN : (109.009173 : ℝ) ≤ √11883 := le_sqrt_of_sq_le (by norm_num)
  have h47 : √(1 + 47 / (11883 : ℝ)) ≤ 1.001976 := sqrt_le_iff.mpr (by norm_num)
  have h95 : √(1 + 95 / (11883 : ℝ)) ≤ 1.00399 := sqrt_le_iff.mpr (by norm_num)
  have h3 : √(1 + 3 / (11883 : ℝ)) ≤ 1.000127 := sqrt_le_iff.mpr (by norm_num)
  have hr := rotation24_upper
  have hrad (j : ℕ) (hj : j ≤ 96) : 0 ≤ radiusCoefficient 11883 j θ := by
    unfold radiusCoefficient
    have hjR : (j : ℝ) ≤ 96 := by exact_mod_cast hj
    have hjc : (2 * j + 2 : ℝ) ≤ 194 := by linarith
    have hp := mul_le_mul hjc (hT.trans hT1) hθ (by norm_num : (0 : ℝ) ≤ 194)
    apply div_nonneg hθ
    simp only [Nat.cast_ofNat]
    nlinarith
  have hr1 := hrad 1 (by norm_num)
  have hr4 := hrad 4 (by norm_num)
  have hr24 := hrad 24 (by norm_num)
  have hr48 := hrad 48 (by norm_num)
  have hr96 := hrad 96 (by norm_num)
  have hslope := BstLean.Part219.kernelSlope_nonneg (1 - θ)
  have hAmp : 0 ≤ paperAmplitude 11883 θ := by unfold paperAmplitude; positivity
  have hrot := BstLean.Part195.rotationConstant_nonneg 24
  unfold paperIdeal paperBias
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hscalar
  gcongr


theorem idealCell0_11883 {θ e : ℝ} (hw : θ ∈ Icc (0.47199 : ℝ) 0.4744)
    (he : 0.665 ≤ e) : paperIdeal 11883 θ e ≤ 0.2292 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 11883 θ ≤ 0.72670100 :=
    amplitude_upper_11883 hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : BstLean.Part219.kernelSlope (1 - θ) ≤ 0.48526907 := by
    apply BstLean.Part253.slope_upper (Q := (0.52801 : ℝ)) (K := (0.62790227 : ℝ)) (s := (0.84923816 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 11883 1 θ ≤ 0.47447577 :=
    radius_upper_11883 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 11883 4 θ ≤ 0.47458947 :=
    radius_upper_11883 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 11883 24 θ ≤ 0.47534886 :=
    radius_upper_11883 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 11883 48 θ ≤ 0.47626334 :=
    radius_upper_11883 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 11883 96 θ ≤ 0.47810290 :=
    radius_upper_11883 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds_11883 hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.47534886 : ℝ) ≤ 0.68945549 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.47447577 : ℝ) / 11883) ≤ 0.00631894 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.4744 : ℝ) ≤ 0.68876702 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.48526907 : ℝ) * 0.72670100 * 0.47626334 * 1.001976 / 0.815475 +
        (77 / 100) * 0.68945549 / 0.815475 *
          (0.00631894 + 0.72670100 * 6.7 * 0.47810290 * 1.00399 / 109.009173 +
            2 * ((0.4744 + 0.68876702 * 0.47458947 * 1.000127) / 11883)) := by gcongr
    _ ≤ (0.2292 : ℝ) := by norm_num

theorem idealCell1_11883 {θ e : ℝ} (hw : θ ∈ Icc (0.4744 : ℝ) 0.4816)
    (he : 0.665 ≤ e) : paperIdeal 11883 θ e ≤ 0.2292 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 11883 θ ≤ 0.72504154 :=
    amplitude_upper_11883 hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : BstLean.Part219.kernelSlope (1 - θ) ≤ 0.48416285 := by
    apply BstLean.Part253.slope_upper (Q := (0.5256 : ℝ)) (K := (0.62626878 : ℝ)) (s := (0.85073183 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 11883 1 θ ≤ 0.48167809 :=
    radius_upper_11883 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 11883 4 θ ≤ 0.48179527 :=
    radius_upper_11883 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 11883 24 θ ≤ 0.48257791 :=
    radius_upper_11883 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 11883 48 θ ≤ 0.48352045 :=
    radius_upper_11883 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 11883 96 θ ≤ 0.48541661 :=
    radius_upper_11883 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds_11883 hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.48257791 : ℝ) ≤ 0.69467828 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.48167809 : ℝ) / 11883) ≤ 0.00636672 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.4816 : ℝ) ≤ 0.69397407 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.48416285 : ℝ) * 0.72504154 * 0.48352045 * 1.001976 / 0.815475 +
        (77 / 100) * 0.69467828 / 0.815475 *
          (0.00636672 + 0.72504154 * 6.7 * 0.48541661 * 1.00399 / 109.009173 +
            2 * ((0.4816 + 0.69397407 * 0.48179527 * 1.000127) / 11883)) := by gcongr
    _ ≤ (0.2292 : ℝ) := by norm_num

theorem idealCell2_11883 {θ e : ℝ} (hw : θ ∈ Icc (0.4816 : ℝ) 0.4888)
    (he : 0.665 ≤ e) : paperIdeal 11883 θ e ≤ 0.2292 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 11883 θ ≤ 0.72005925 :=
    amplitude_upper_11883 hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : BstLean.Part219.kernelSlope (1 - θ) ≤ 0.48088081 := by
    apply BstLean.Part253.slope_upper (Q := (0.5184 : ℝ)) (K := (0.62140204 : ℝ)) (s := (0.85513826 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 11883 1 θ ≤ 0.48888044 :=
    radius_upper_11883 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 11883 4 θ ≤ 0.48900115 :=
    radius_upper_11883 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 11883 24 θ ≤ 0.48980740 :=
    radius_upper_11883 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 11883 48 θ ≤ 0.49077842 :=
    radius_upper_11883 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 11883 96 θ ≤ 0.49273204 :=
    radius_upper_11883 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds_11883 hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.48980740 : ℝ) ≤ 0.69986242 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.48888044 : ℝ) / 11883) ≤ 0.00641414 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.4888 : ℝ) ≤ 0.69914234 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.48088081 : ℝ) * 0.72005925 * 0.49077842 * 1.001976 / 0.815475 +
        (77 / 100) * 0.69986242 / 0.815475 *
          (0.00641414 + 0.72005925 * 6.7 * 0.49273204 * 1.00399 / 109.009173 +
            2 * ((0.4888 + 0.69914234 * 0.48900115 * 1.000127) / 11883)) := by gcongr
    _ ≤ (0.2292 : ℝ) := by norm_num

theorem idealCell3_11883 {θ e : ℝ} (hw : θ ∈ Icc (0.4888 : ℝ) 0.496)
    (he : 0.665 ≤ e) : paperIdeal 11883 θ e ≤ 0.2292 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 11883 θ ≤ 0.71504222 :=
    amplitude_upper_11883 hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : BstLean.Part219.kernelSlope (1 - θ) ≤ 0.47763237 := by
    apply BstLean.Part253.slope_upper (Q := (0.5112 : ℝ)) (K := (0.61655526 : ℝ)) (s := (0.85946179 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 11883 1 θ ≤ 0.49608283 :=
    radius_upper_11883 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 11883 4 θ ≤ 0.49620712 :=
    radius_upper_11883 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 11883 24 θ ≤ 0.49703733 :=
    radius_upper_11883 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 11883 48 θ ≤ 0.49803725 :=
    radius_upper_11883 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 11883 96 θ ≤ 0.50004921 :=
    radius_upper_11883 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds_11883 hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.49703733 : ℝ) ≤ 0.70500875 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.49608283 : ℝ) / 11883) ≤ 0.00646122 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.496 : ℝ) ≤ 0.70427268 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.47763237 : ℝ) * 0.71504222 * 0.49803725 * 1.001976 / 0.815475 +
        (77 / 100) * 0.70500875 / 0.815475 *
          (0.00646122 + 0.71504222 * 6.7 * 0.50004921 * 1.00399 / 109.009173 +
            2 * ((0.496 + 0.70427268 * 0.49620712 * 1.000127) / 11883)) := by gcongr
    _ ≤ (0.2292 : ℝ) := by norm_num

theorem idealCell4_11883 {θ e : ℝ} (hw : θ ∈ Icc (0.496 : ℝ) 0.5032)
    (he : 0.665 ≤ e) : paperIdeal 11883 θ e ≤ 0.2292 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 11883 θ ≤ 0.70998971 :=
    amplitude_upper_11883 hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : BstLean.Part219.kernelSlope (1 - θ) ≤ 0.47441674 := by
    apply BstLean.Part253.slope_upper (Q := (0.504 : ℝ)) (K := (0.61172830 : ℝ)) (s := (0.86370366 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 11883 1 θ ≤ 0.50328525 :=
    radius_upper_11883 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 11883 4 θ ≤ 0.50341318 :=
    radius_upper_11883 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 11883 24 θ ≤ 0.50426770 :=
    radius_upper_11883 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 11883 48 θ ≤ 0.50529695 :=
    radius_upper_11883 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 11883 96 θ ≤ 0.50736812 :=
    radius_upper_11883 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds_11883 hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.50426770 : ℝ) ≤ 0.71011809 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.50328525 : ℝ) / 11883) ≤ 0.00650795 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.5032 : ℝ) ≤ 0.70936592 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.47441674 : ℝ) * 0.70998971 * 0.50529695 * 1.001976 / 0.815475 +
        (77 / 100) * 0.71011809 / 0.815475 *
          (0.00650795 + 0.70998971 * 6.7 * 0.50736812 * 1.00399 / 109.009173 +
            2 * ((0.5032 + 0.70936592 * 0.50341318 * 1.000127) / 11883)) := by gcongr
    _ ≤ (0.2292 : ℝ) := by norm_num

theorem idealCell5_11883 {θ e : ℝ} (hw : θ ∈ Icc (0.5032 : ℝ) 0.5104)
    (he : 0.665 ≤ e) : paperIdeal 11883 θ e ≤ 0.2292 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 11883 θ ≤ 0.70490097 :=
    amplitude_upper_11883 hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : BstLean.Part219.kernelSlope (1 - θ) ≤ 0.47123312 := by
    apply BstLean.Part253.slope_upper (Q := (0.4968 : ℝ)) (K := (0.60692102 : ℝ)) (s := (0.86786506 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 11883 1 θ ≤ 0.51048771 :=
    radius_upper_11883 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 11883 4 θ ≤ 0.51061933 :=
    radius_upper_11883 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 11883 24 θ ≤ 0.51149850 :=
    radius_upper_11883 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 11883 48 θ ≤ 0.51255752 :=
    radius_upper_11883 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 11883 96 θ ≤ 0.51468876 :=
    radius_upper_11883 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds_11883 hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.51149850 : ℝ) ≤ 0.71519124 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.51048771 : ℝ) / 11883) ≤ 0.00655435 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.5104 : ℝ) ≤ 0.71442285 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.47123312 : ℝ) * 0.70490097 * 0.51255752 * 1.001976 / 0.815475 +
        (77 / 100) * 0.71519124 / 0.815475 *
          (0.00655435 + 0.70490097 * 6.7 * 0.51468876 * 1.00399 / 109.009173 +
            2 * ((0.5104 + 0.71442285 * 0.51061933 * 1.000127) / 11883)) := by gcongr
    _ ≤ (0.2292 : ℝ) := by norm_num

theorem idealCell6_11883 {θ e : ℝ} (hw : θ ∈ Icc (0.5104 : ℝ) 0.5176)
    (he : 0.665 ≤ e) : paperIdeal 11883 θ e ≤ 0.2292 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 11883 θ ≤ 0.69977520 :=
    amplitude_upper_11883 hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : BstLean.Part219.kernelSlope (1 - θ) ≤ 0.46808077 := by
    apply BstLean.Part253.slope_upper (Q := (0.4896 : ℝ)) (K := (0.60213330 : ℝ)) (s := (0.87194716 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 11883 1 θ ≤ 0.51769020 :=
    radius_upper_11883 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 11883 4 θ ≤ 0.51782556 :=
    radius_upper_11883 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 11883 24 θ ≤ 0.51872975 :=
    radius_upper_11883 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 11883 48 θ ≤ 0.51981895 :=
    radius_upper_11883 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 11883 96 θ ≤ 0.52201113 :=
    radius_upper_11883 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds_11883 hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.51872975 : ℝ) ≤ 0.72022896 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.51769020 : ℝ) / 11883) ≤ 0.00660043 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.5176 : ℝ) ≤ 0.71944423 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.46808077 : ℝ) * 0.69977520 * 0.51981895 * 1.001976 / 0.815475 +
        (77 / 100) * 0.72022896 / 0.815475 *
          (0.00660043 + 0.69977520 * 6.7 * 0.52201113 * 1.00399 / 109.009173 +
            2 * ((0.5176 + 0.71944423 * 0.51782556 * 1.000127) / 11883)) := by gcongr
    _ ≤ (0.2292 : ℝ) := by norm_num

theorem idealCell7_11883 {θ e : ℝ} (hw : θ ∈ Icc (0.5176 : ℝ) 0.52358)
    (he : 0.665 ≤ e) : paperIdeal 11883 θ e ≤ 0.2292 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 11883 θ ≤ 0.69461143 :=
    amplitude_upper_11883 hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : BstLean.Part219.kernelSlope (1 - θ) ≤ 0.46495896 := by
    apply BstLean.Part253.slope_upper (Q := (0.4824 : ℝ)) (K := (0.59736500 : ℝ)) (s := (0.87595105 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 11883 1 θ ≤ 0.52367230 :=
    radius_upper_11883 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 11883 4 θ ≤ 0.52381080 :=
    radius_upper_11883 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 11883 24 θ ≤ 0.52473603 :=
    radius_upper_11883 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 11883 48 θ ≤ 0.52585063 :=
    radius_upper_11883 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 11883 96 θ ≤ 0.52809409 :=
    radius_upper_11883 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds_11883 hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.52473603 : ℝ) ≤ 0.72438666 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.52367230 : ℝ) / 11883) ≤ 0.00663846 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.52358 : ℝ) ≤ 0.72358829 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.46495896 : ℝ) * 0.69461143 * 0.52585063 * 1.001976 / 0.815475 +
        (77 / 100) * 0.72438666 / 0.815475 *
          (0.00663846 + 0.69461143 * 6.7 * 0.52809409 * 1.00399 / 109.009173 +
            2 * ((0.52358 + 0.72358829 * 0.52381080 * 1.000127) / 11883)) := by gcongr
    _ ≤ (0.2292 : ℝ) := by norm_num

theorem ideal_window_11883 {θ e : ℝ} (hw : θ ∈ Icc (0.47199 : ℝ) 0.52358)
    (he : 0.665 ≤ e) : paperIdeal 11883 θ e ≤ 0.2292 := by
  by_cases h1 : θ ≤ 0.4744
  · exact idealCell0_11883 ⟨hw.1, h1⟩ he
  by_cases h2 : θ ≤ 0.4816
  · exact idealCell1_11883 ⟨by linarith, h2⟩ he
  by_cases h3 : θ ≤ 0.4888
  · exact idealCell2_11883 ⟨by linarith, h3⟩ he
  by_cases h4 : θ ≤ 0.496
  · exact idealCell3_11883 ⟨by linarith, h4⟩ he
  by_cases h5 : θ ≤ 0.5032
  · exact idealCell4_11883 ⟨by linarith, h5⟩ he
  by_cases h6 : θ ≤ 0.5104
  · exact idealCell5_11883 ⟨by linarith, h6⟩ he
  by_cases h7 : θ ≤ 0.5176
  · exact idealCell6_11883 ⟨by linarith, h7⟩ he
  exact idealCell7_11883 ⟨by linarith, hw.2⟩ he


theorem direction_budget_11883 {n : ℕ} (hn : 11883 ≤ n)
    (c : Fin n → ℝ) (τ e xi eta : ℝ) (δ : ℝ≥0∞)
    (hw : BstLean.Part150.thetaC c τ ∈ Icc (0.47199 : ℝ) 0.52358)
    (he : 0.665 ≤ e) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.1)
    (hop : operatorAllowance c τ eta δ ^ 2 ≤ 1.25) :
    paperDirectionBudget c τ e xi eta δ ≤ (0.0898 : ℝ) := by
  have hroot : (0.88 : ℝ) ≤ (7 / 25000 : ℝ) ^ (1 / 64 : ℝ) := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (64 : ℕ) ≠ 0) (by positivity)
    have hh := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 7 / 25000)
      (by norm_num : (64 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hh
    rw [hh]
    norm_num
  have h := BstLean.Part277.direction_budget_leP (n0 := 11883) (by norm_num) hn c τ e xi eta δ
    (θlo := 0.47199) (θhi := 0.52358) (e0 := 0.665) (xi0 := 0.1) (MP := 1.25)
    (I0 := 0.2292) (ε0 := 0.0658) (Rc := 0.525) (sR := 0.889) (ρ0 := 0.88)
    (by norm_num) hw (by norm_num) (by norm_num) he hxi hxi1 hop (by norm_num)
    (fun θ hθ e' he' => ideal_window_11883 hθ (by linarith))
    (fun θ hθ => radius_upper_11883 12 (le_trans (by norm_num) hθ.1) hθ.2
      (by norm_num) (by norm_num))
    error_epsilon_upper_11883 (by norm_num) (by norm_num) (by norm_num) hroot
  refine h.trans ?_
  have hs : √((1.25 : ℝ) * 0.1 / ((11883 : ℕ) * 0.665)) ≤ 0.00398 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    norm_num
  calc _ ≤ ((0.2292 : ℝ) + 0.0658 * 0.889 / 0.88 + 0.00398) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part281.Dir11883

