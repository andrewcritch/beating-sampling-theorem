import BstLean.Part253DirectionConstants
import BstLean.Part277Mono

/-! A coarse endpoint bound for the actual Part219 error term.
The low-length root is re-proved at 8000; the higher-band root is not reused. -/
namespace BstLean.BlueprintLow
open Real BstLean.Part152 BstLean.Part209 BstLean.Part253

theorem lowLengthRoot8000 : lowLengthProb 8000 (1 / 100) ^ (1 / 128 : ℝ) ≤
    (1 / 2000 : ℝ) := by
  have hp : 0 ≤ lowLengthProb 8000 (1 / 100) := by unfold lowLengthProb; positivity
  have hexp : exp (-(8000 : ℝ) ^ 2 * (1 / 100 - 2 / (8000 : ℝ) ^ 2) ^ 2 / 4) ≤
      (1 / 2 : ℝ) ^ 1536 := by
    calc
      _ ≤ exp (1536 * (-1 : ℝ)) := exp_le_exp.mpr (by norm_num)
      _ = exp (-1 : ℝ) ^ 1536 := by simpa using exp_nat_mul (-1 : ℝ) 1536
      _ ≤ _ := pow_le_pow_left₀ (exp_pos _).le exp_minus_one_half _
  have hpow : lowLengthProb 8000 (1 / 100) ≤ (1 / 2000 : ℝ) ^ 128 := by
    unfold lowLengthProb
    calc
      _ ≤ 4 * (1 / 2 : ℝ) ^ 1536 := mul_le_mul_of_nonneg_left hexp (by norm_num)
      _ = 4 * ((1 / 2 : ℝ) ^ 12) ^ 128 := by rw [← pow_mul]
      _ ≤ (2 : ℝ) ^ 128 * ((1 / 2 : ℝ) ^ 12) ^ 128 := by gcongr; norm_num
      _ = ((2 : ℝ) * (1 / 2) ^ 12) ^ 128 := by rw [mul_pow]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (by norm_num) _
  have h := root_upper (by norm_num : (128 : ℕ) ≠ 0) hp (by norm_num) hpow
  norm_num only [Nat.cast_ofNat] at h
  exact h

theorem lengthAlpha8000 (P : ℕ) {b B : ℝ} (hb : twoGaussConst P ≤ b)
    (hnum : 2 / (8000 : ℝ) ^ 2 + 1.414213563 / 8000 * b ≤ B) :
    lengthAlpha 8000 P ≤ B := by
  have hs : √(2 : ℝ) ≤ 1.414213563 := sqrt_le_iff.mpr (by norm_num)
  have hb0 := twoGaussConst_nonneg P
  unfold lengthAlpha
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hnum
  gcongr

theorem length16_8000 : lengthAlpha 8000 16 ≤ 0.000667 :=
  lengthAlpha8000 16 two16_upper (by norm_num)
theorem length32_8000 : lengthAlpha 8000 32 ≤ 0.000904 :=
  lengthAlpha8000 32 two32_upper (by norm_num)
theorem length64_8000 : lengthAlpha 8000 64 ≤ 0.001249 :=
  lengthAlpha8000 64 two64_upper (by norm_num)
theorem length128_8000 : lengthAlpha 8000 128 ≤ 0.001743 :=
  lengthAlpha8000 128 two128_upper (by norm_num)

theorem pairQ8000 : pairQ 8000 32 ≤ 0.016721 := by
  have h0 := gaussMomConst_nonneg 32
  have hs : √(8000 : ℝ) ≤ 89.44272 := sqrt_le_iff.mpr (by norm_num)
  have hs2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hg := gauss32_upper
  unfold pairQ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 / (8000 : ℝ) ^ 2 * (89.44272 + 5.05772465) *
        (8000 / 1.414213562 + 5.05772465) := by gcongr
    _ ≤ (0.016721 : ℝ) := by norm_num

theorem pairPlane8000 : pairPlane 8000 32 ≤ 382938 := by
  have hs : √(32 : ℝ) ≤ 5.65685425 := sqrt_le_iff.mpr (by norm_num)
  have hl := log162_upper
  have h32 := factorial32_upper
  have h64 := factorial64_upper
  have hr : √(log (162 : ℝ) + factorialRoot 32) ≤ 4.22827381 := by
    apply sqrt_le_iff.mpr
    exact ⟨by norm_num, by linarith⟩
  unfold pairPlane
  simp only [Nat.cast_ofNat, Nat.reduceMul]
  calc
    _ ≤ 2 * 5.65685425 * (8000 : ℝ) * 4.22827381 +
        8 * (5.088 + 24.67407549) := by gcongr
    _ ≤ (382938 : ℝ) := by norm_num

theorem pairV8000 : pairV 8000 32 ≤ 0.028688 := by
  have hq := pairQ8000
  have hp := pairPlane8000
  unfold pairV
  simp only [Nat.cast_ofNat]
  linarith

theorem overlap8000 : overlapC 8000 16 ≤ 0.003770334 := by
  have hs : √(32 : ℝ) ≤ 5.65685425 := sqrt_le_iff.mpr (by norm_num)
  have h16 := overlap16_upper
  have h32 := overlap32_upper
  unfold overlapC
  simp only [Nat.cast_ofNat, Nat.reduceMul]
  rw [show (2 * (16 : ℝ)) = 32 by norm_num]
  calc
    _ ≤ 2 / (8000 : ℝ) ^ 2 *
        (5.65685425 * 8000 * 2.66487321 + 4 * 13.07036015) := by gcongr
    _ ≤ (0.003770334 : ℝ) := by norm_num

theorem delta8000 : pairDelta 8000 16 (1 / 100) ≤ 0.00521 := by
  have ho := overlap8000
  have h16 := length16_8000
  have h32 := length32_8000
  have h0 := lengthAlpha_nonneg 8000 32
  unfold pairDelta
  simp only [Nat.reduceMul]
  calc
    _ ≤ ((0.003770334 : ℝ) + 2 * 0.000667 + 0.000904 ^ 2) / (1 - 1 / 100) ^ 2 := by gcongr
    _ ≤ (0.00521 : ℝ) := by norm_num

theorem tangent8000 (P : ℕ) {b g r B : ℝ}
    (hb : twoGaussConst P ≤ b) (hg : gaussMomConst (2 * P) ≤ g)
    (hr0 : 0 ≤ r) (hr : (8000 : ℝ) ^ 2 / 2 + 8000 / 2 * b ≤ r ^ 2)
    (hnum : 2 / (8000 : ℝ) ^ 2 * (r + 89.44272 + g) ^ 2 ≤ B) :
    tangentU 8000 P ≤ B := by
  have hs : √((8000 : ℝ) ^ 2 / 2 + activeB 8000 P) ≤ r := by
    apply sqrt_le_iff.mpr
    refine ⟨hr0, ?_⟩
    unfold activeB
    simp only [Nat.cast_ofNat]
    nlinarith
  have hn : √(8000 : ℝ) ≤ 89.44272 := sqrt_le_iff.mpr (by norm_num)
  have h0 := gaussMomConst_nonneg (2 * P)
  unfold tangentU
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hnum
  gcongr

theorem tangent32_8000 : tangentU 8000 32 ≤ 1.03505 := by
  apply tangent8000 32 two32_upper gauss64_upper (r := 5658.661609) <;> norm_num
theorem tangent64_8000 : tangentU 8000 64 ≤ 1.03631 := by
  apply tangent8000 64 two64_upper gauss128_upper (r := 5659.350835) <;> norm_num

theorem directionError8000 : pairEpsilon 8000 16 (1 / 100) ≤ 0.087 := by
  have hV := pairV8000
  have hQ := pairQ8000
  have hQ0 := pairQ_nonneg 8000 32
  have hV0 := pairV_nonneg 8000 32
  have hd : √(pairDelta 8000 16 (1 / 100)) ≤ 0.072181 :=
    sqrt_le_iff.mpr ⟨by norm_num, delta8000.trans (by norm_num)⟩
  have ht32 : √(tangentU 8000 32) ≤ 1.017375 :=
    sqrt_le_iff.mpr ⟨by norm_num, tangent32_8000.trans (by norm_num)⟩
  have ht64 : √(tangentU 8000 64) ≤ 1.017995 :=
    sqrt_le_iff.mpr ⟨by norm_num, tangent64_8000.trans (by norm_num)⟩
  have hl64 := length64_8000
  have hl128 := length128_8000
  have hl0 := lengthAlpha_nonneg 8000 128
  have hrad : radialCoefficient (1 / 100) ≤ 0.324741 := by
    unfold radialCoefficient
    apply (div_le_iff₀ (by positivity : 0 < π * (1 - 1 / 100))).mpr
    linarith [pi_gt_d6]
  have hlow := lowLengthRoot8000
  have hlow0 : 0 ≤ lowLengthProb 8000 (1 / 100) ^ (1 / 128 : ℝ) :=
    rpow_nonneg (by unfold lowLengthProb; positivity) _
  have hcomp : complementB 8000 16 (1 / 100) ≤
      (1.017995 * (1 + 0.001743) + 1) * (1 / 2000 : ℝ) := by
    unfold complementB complementRoot
    simp only [Nat.reduceMul, Nat.cast_ofNat]
    rw [show (8 * (16 : ℝ)) = 128 by norm_num]
    gcongr
  have hfluc : fluctuationRoot 8000 16 ≤ (0.028688 : ℝ) * 1.017375 * (1 + 0.001249) := by
    have hl640 := lengthAlpha_nonneg 8000 64
    have hprod := mul_le_mul hV ht32 (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 0.028688)
    have hh := mul_le_mul hprod (add_le_add (le_refl (1 : ℝ)) hl64)
      (by linarith : (0 : ℝ) ≤ 1 + lengthAlpha 8000 64) (by norm_num)
    simpa only [fluctuationRoot, Nat.reduceMul] using hh
  have hmean : meanEpsilon 8000 16 (1 / 100) ≤
      0.028688 + (3 / 10 : ℝ) * 0.072181 + 0.324741 * 0.016721 +
        (1.017995 * (1 + 0.001743) + 1) * (1 / 2000) := by
    have hh := add_le_add (add_le_add (add_le_add hV
      (mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 3 / 10)))
      (mul_le_mul hrad hQ hQ0 (by norm_num : (0 : ℝ) ≤ 0.324741))) hcomp
    simpa only [meanEpsilon, Nat.reduceMul] using hh
  unfold pairEpsilon
  linarith

end BstLean.BlueprintLow
