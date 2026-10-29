import BstLean.Part253DirectionConstants

/-! The actual Part219 direction error has a rational upper bound. -/
namespace BstLean.Part253
open Real BstLean.Part152 BstLean.Part209

theorem sqrtN_upper : √(12225 : ℝ) ≤ 110.566722 := sqrt_le_iff.mpr (by norm_num)
theorem sqrt2_upper : √(2 : ℝ) ≤ 1.414213563 := sqrt_le_iff.mpr (by norm_num)
theorem sqrt2_lower : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
theorem sqrt32_upper : √(32 : ℝ) ≤ 5.65685425 := sqrt_le_iff.mpr (by norm_num)

theorem length_upper (P : ℕ) {b B : ℝ} (hb : twoGaussConst P ≤ b)
    (hnum : 2 / (12225 : ℝ) ^ 2 + 1.414213563 / 12225 * b ≤ B) :
    lengthAlpha 12225 P ≤ B := by
  unfold lengthAlpha
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hnum
  have h0 := twoGaussConst_nonneg P
  gcongr
  exact sqrt2_upper

theorem length16_upper : lengthAlpha 12225 16 ≤ 0.000436 :=
  length_upper 16 two16_upper (by norm_num)
theorem length32_upper : lengthAlpha 12225 32 ≤ 0.00059148 :=
  length_upper 32 two32_upper (by norm_num)
theorem length64_upper : lengthAlpha 12225 64 ≤ 0.00081708 :=
  length_upper 64 two64_upper (by norm_num)
theorem length128_upper : lengthAlpha 12225 128 ≤ 0.00114051 :=
  length_upper 128 two128_upper (by norm_num)

theorem pairQ_upper : pairQ 12225 32 ≤ 0.013384 := by
  have h0 := gaussMomConst_nonneg 32
  have hs := sqrtN_upper
  have hs2 := sqrt2_lower
  have hg := gauss32_upper
  unfold pairQ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 / (12225 : ℝ) ^ 2 * (110.566722 + 5.05772465) *
        (12225 / 1.414213562 + 5.05772465) := by gcongr
    _ ≤ (0.013384 : ℝ) := by norm_num

theorem pairPlane_upper : pairPlane 12225 32 ≤ 585052 := by
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
    _ ≤ 2 * 5.65685425 * (12225 : ℝ) * 4.22827381 +
        8 * (5.088 + 24.67407549) := by gcongr
    _ ≤ (585052 : ℝ) := by norm_num

theorem pairV_upper : pairV 12225 32 ≤ 0.021214 := by
  unfold pairV
  have hq := pairQ_upper
  have hp := pairPlane_upper
  simp only [Nat.cast_ofNat]
  linarith

theorem overlap_upper : overlapC 12225 16 ≤ 0.002466925 := by
  have hs := sqrt32_upper
  have h16 := overlap16_upper
  have h32 := overlap32_upper
  unfold overlapC
  simp only [Nat.cast_ofNat, Nat.reduceMul]
  rw [show (2 * (16 : ℝ)) = 32 by norm_num]
  calc
    _ ≤ 2 / (12225 : ℝ) ^ 2 *
        (5.65685425 * 12225 * 2.66487321 + 4 * 13.07036015) := by gcongr
    _ ≤ (0.002466925 : ℝ) := by norm_num

theorem delta_upper : pairDelta 12225 16 (1 / 100) ≤ 0.0034071 := by
  have ho := overlap_upper
  have h16 := length16_upper
  have h32 := length32_upper
  have h0 := lengthAlpha_nonneg 12225 32
  unfold pairDelta
  simp only [Nat.reduceMul]
  calc
    _ ≤ ((0.002466925 : ℝ) + 2 * 0.000436 + 0.00059148 ^ 2) / (1 - 1 / 100) ^ 2 := by
      gcongr
    _ ≤ (0.0034071 : ℝ) := by norm_num

theorem tangent_upper (P : ℕ) {b g r B : ℝ}
    (hb : twoGaussConst P ≤ b) (hg : gaussMomConst (2 * P) ≤ g)
    (hr0 : 0 ≤ r) (hr : (12225 : ℝ) ^ 2 / 2 + 12225 / 2 * b ≤ r ^ 2)
    (hnum : 2 / (12225 : ℝ) ^ 2 * (r + 110.566722 + g) ^ 2 ≤ B) :
    tangentU 12225 P ≤ B := by
  have hs : √((12225 : ℝ) ^ 2 / 2 + activeB 12225 P) ≤ r := by
    apply sqrt_le_iff.mpr
    refine ⟨hr0, ?_⟩
    unfold activeB
    simp only [Nat.cast_ofNat]
    nlinarith
  have hn := sqrtN_upper
  have h0 := gaussMomConst_nonneg (2 * P)
  unfold tangentU
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hnum
  gcongr

theorem tangent32_upper : tangentU 12225 32 ≤ 1.027816 := by
  apply tangent_upper 32 two32_upper gauss64_upper (r := 8646.18786)
    <;> norm_num

theorem tangent64_upper : tangentU 12225 64 ≤ 1.028637 := by
  apply tangent_upper 64 two64_upper gauss128_upper (r := 8646.87718)
    <;> norm_num

theorem error_epsilon_upper : pairEpsilon 12225 16 (1 / 100) ≤ 0.0647 := by
  have hV := pairV_upper
  have hQ := pairQ_upper
  have hQ0 := pairQ_nonneg 12225 32
  have hV0 := pairV_nonneg 12225 32
  have hd : √(pairDelta 12225 16 (1 / 100)) ≤ 0.058371 :=
    sqrt_le_iff.mpr ⟨by norm_num, delta_upper.trans (by norm_num)⟩
  have ht32 : √(tangentU 12225 32) ≤ 1.0138131 :=
    sqrt_le_iff.mpr ⟨by norm_num, tangent32_upper.trans (by norm_num)⟩
  have ht64 : √(tangentU 12225 64) ≤ 1.0142185 :=
    sqrt_le_iff.mpr ⟨by norm_num, tangent64_upper.trans (by norm_num)⟩
  have hl64 := length64_upper
  have hl128 := length128_upper
  have hl0 := lengthAlpha_nonneg 12225 128
  have hrad : radialCoefficient (1 / 100) ≤ 0.324741 := by
    unfold radialCoefficient
    apply (div_le_iff₀ (by positivity : 0 < π * (1 - 1 / 100))).mpr
    linarith [pi_gt_d6]
  have hr0 := radialCoefficient_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 100)
    (by norm_num : (1 / 100 : ℝ) < 1)
  have hlow := low_length_root
  have hlow0 : 0 ≤ lowLengthProb 12225 (1 / 100) ^ (1 / 128 : ℝ) :=
    rpow_nonneg (by unfold lowLengthProb; positivity) _
  have hcomp : complementB 12225 16 (1 / 100) ≤
      (1.0142185 * (1 + 0.00114051) + 1) * (1 / 1000000 : ℝ) := by
    unfold complementB complementRoot
    simp only [Nat.reduceMul, Nat.cast_ofNat]
    rw [show (8 * (16 : ℝ)) = 128 by norm_num]
    gcongr
  have hfluc : fluctuationRoot 12225 16 ≤
      (0.021214 : ℝ) * 1.0138131 * (1 + 0.00081708) := by
    have hl640 := lengthAlpha_nonneg 12225 64
    have hprod := mul_le_mul hV ht32 (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 0.021214)
    have hh := mul_le_mul hprod (add_le_add (le_refl (1 : ℝ)) hl64)
      (by linarith : (0 : ℝ) ≤ 1 + lengthAlpha 12225 64) (by norm_num)
    simpa only [fluctuationRoot, Nat.reduceMul] using hh
  have hmean : meanEpsilon 12225 16 (1 / 100) ≤
      0.021214 + (3 / 10 : ℝ) * 0.058371 + 0.324741 * 0.013384 +
        (1.0142185 * (1 + 0.00114051) + 1) * (1 / 1000000) := by
    have hh := add_le_add (add_le_add (add_le_add hV
      (mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 3 / 10)))
      (mul_le_mul hrad hQ hQ0 (by norm_num : (0 : ℝ) ≤ 0.324741))) hcomp
    simpa only [meanEpsilon, Nat.reduceMul] using hh
  unfold pairEpsilon
  linarith

end BstLean.Part253
