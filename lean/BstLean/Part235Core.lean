import BstLean.Part235Geometry

/-! Part 235: checked core geometry from dimension 11883. -/
namespace BstLean.Part235
open Real BstLean.Part199

theorem core_overlap_guard {n : ℕ} (hn : 11883 ≤ n) {θ : ℝ}
    (hθlo : 46 / 100 ≤ θ) (hθhi : θ ≤ 528 / 1000) :
    OverlapGuard n θ exampleCore (40 / 100) (63 / 100) := by
  have hnR : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0 : 0 ≤ θ := by linarith
  have h1θ : 0 < 1 - θ := by linarith
  have hs : (109 : ℝ) ≤ √(n : ℝ) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hs0 : 0 < √(n : ℝ) := by linarith
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg n)
  have ha : √(θ * (1 - θ) / n) ≤ 1 / 218 := by
    apply BstLean.Part182.sqrt_le_of_sq' (by norm_num)
    rw [div_le_iff₀ hn0]
    nlinarith [sq_nonneg (θ - 1 / 2)]
  have hz : √((75 / 10 : ℝ) / n) ≤ 26 / 1000 := by
    apply BstLean.Part182.sqrt_le_of_sq' (by norm_num)
    rw [div_le_iff₀ hn0]
    nlinarith
  have hb : planeRatio n θ exampleCore ≤ 28 / 1000 := by
    unfold planeRatio exampleCore
    change (28 / 10) * √(θ / ((1 - θ) * n)) ≤ 28 / 1000
    have hroot : √(θ / ((1 - θ) * n)) ≤ 1 / 100 := by
      apply BstLean.Part182.sqrt_le_of_sq' (by norm_num)
      rw [div_le_iff₀ (mul_pos h1θ hn0)]
      have hmul := mul_le_mul_of_nonneg_left hnR h1θ.le
      nlinarith
    linarith
  have hb0 : 0 ≤ planeRatio n θ exampleCore := by
    unfold planeRatio exampleCore
    positivity
  have hr : radiusMinus n θ exampleCore ≤ 54 / 1000 := by
    have hθz := mul_le_mul hθhi hz (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 528 / 1000)
    unfold radiusMinus exampleCore
    change 2 * (28 / 10) * √(θ * (1 - θ) / n) + 2 * θ * √((75 / 10) / n) ≤ 54 / 1000
    nlinarith
  have hrp : radiusPlus n θ exampleCore ≤ 55 / 1000 := by
    have hθn : θ / (n : ℝ) ≤ (528 / 1000) / 11883 := by
      rw [div_le_div_iff₀ hn0 (by norm_num)]
      nlinarith
    unfold radiusPlus exampleCore
    change radiusMinus n θ exampleCore + 2 * θ * (75 / 10) / n ≤ 55 / 1000
    have he : 2 * θ * (75 / 10) / (n : ℝ) = 15 * (θ / n) := by ring
    rw [he]
    nlinarith
  have hg : BstLean.Part182.gPlus n (75 / 10) ≤ √(n : ℝ) + 3 := by
    apply BstLean.Part182.sqrt_le_of_sq' (by positivity)
    have h20 : √(75 / 10 : ℝ) ≤ 11 / 4 :=
      BstLean.Part182.sqrt_le_of_sq' (by norm_num) (by norm_num)
    have hm := mul_le_mul_of_nonneg_left h20 hs0.le
    rw [Real.sqrt_mul (Nat.cast_nonneg n)]
    nlinarith
  have hgn : BstLean.Part182.gPlus n (75 / 10) / (n : ℝ) ≤ 1 / 109 + 3 / 11883 := by
    have hsn : √(n : ℝ) / (n : ℝ) ≤ 1 / 109 := by
      rw [div_le_iff₀ hn0]
      nlinarith
    have h5n : (3 : ℝ) / n ≤ 3 / 11883 := by
      rw [div_le_iff₀ hn0]
      nlinarith
    have h := div_le_div_of_nonneg_right hg hn0.le
    rw [add_div] at h
    linarith
  have hterm : θ / (n : ℝ) * (32 / 10) * BstLean.Part182.gPlus n (75 / 10) ≤ 17 / 1000 := by
    have hg0 : 0 ≤ BstLean.Part182.gPlus n (75 / 10) / (n : ℝ) := by
      unfold BstLean.Part182.gPlus
      positivity
    have hm := mul_le_mul hθhi hgn hg0 (by norm_num : (0 : ℝ) ≤ 528 / 1000)
    have he : θ / (n : ℝ) * (32 / 10) * BstLean.Part182.gPlus n (75 / 10) =
        (32 / 10) * (θ * (BstLean.Part182.gPlus n (75 / 10) / (n : ℝ))) := by ring
    rw [he]
    nlinarith
  have hupper : (1 - θ) * (1 + planeRatio n θ exampleCore) ^ 2 ≤ (54 / 100) * (1028 / 1000) ^ 2 := by
    apply mul_le_mul (by linarith : 1 - θ ≤ 54 / 100)
      (pow_le_pow_left₀ (by linarith) (by linarith : 1 + planeRatio n θ exampleCore ≤ 1028 / 1000) 2)
      (by positivity) (by norm_num)
  have hlower : (472 / 1000) * (972 / 1000) ^ 2 ≤ (1 - θ) * (1 - planeRatio n θ exampleCore) ^ 2 := by
    apply mul_le_mul (by linarith : 472 / 1000 ≤ 1 - θ)
      (pow_le_pow_left₀ (by norm_num) (by linarith : 972 / 1000 ≤ 1 - planeRatio n θ exampleCore) 2)
      (by positivity) h1θ.le
  refine ⟨hθ0, by linarith, by linarith, by linarith, by norm_num, ?_, ?_⟩
  · unfold overlapNumerator
    simp only [neg_one_mul, sub_eq_add_neg]
    change 40 / 100 * (1 + radiusPlus n θ exampleCore) ≤
      (1 - θ) * (1 - planeRatio n θ exampleCore) ^ 2 - θ / n * (32 / 10) * BstLean.Part182.gPlus n (75 / 10)
    nlinarith
  · unfold overlapNumerator
    simp only [one_mul]
    change (1 - θ) * (1 + planeRatio n θ exampleCore) ^ 2 +
      θ / n * (32 / 10) * BstLean.Part182.gPlus n (75 / 10) ≤ 63 / 100 * (1 - radiusMinus n θ exampleCore)
    nlinarith


/-- The exact radius formulas have uniform rational upper bounds. -/
theorem core_radius_caps {n : ℕ} (hn : 11883 ≤ n) {θ : ℝ}
    (hθlo : 46 / 100 ≤ θ) (hθhi : θ ≤ 528 / 1000) :
    radiusMinus n θ exampleCore ≤ 54 / 1000 ∧ radiusPlus n θ exampleCore ≤ 55 / 1000 := by
  have hnR : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0 : 0 ≤ θ := by linarith
  have h1θ : 0 < 1 - θ := by linarith
  have hs : (109 : ℝ) ≤ √(n : ℝ) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hs0 : 0 < √(n : ℝ) := by linarith
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg n)
  have ha : √(θ * (1 - θ) / n) ≤ 1 / 218 := by
    apply BstLean.Part182.sqrt_le_of_sq' (by norm_num)
    rw [div_le_iff₀ hn0]
    nlinarith [sq_nonneg (θ - 1 / 2)]
  have hz : √((75 / 10 : ℝ) / n) ≤ 26 / 1000 := by
    apply BstLean.Part182.sqrt_le_of_sq' (by norm_num)
    rw [div_le_iff₀ hn0]
    nlinarith
  have hb : planeRatio n θ exampleCore ≤ 28 / 1000 := by
    unfold planeRatio exampleCore
    change (28 / 10) * √(θ / ((1 - θ) * n)) ≤ 28 / 1000
    have hroot : √(θ / ((1 - θ) * n)) ≤ 1 / 100 := by
      apply BstLean.Part182.sqrt_le_of_sq' (by norm_num)
      rw [div_le_iff₀ (mul_pos h1θ hn0)]
      have hmul := mul_le_mul_of_nonneg_left hnR h1θ.le
      nlinarith
    linarith
  have hb0 : 0 ≤ planeRatio n θ exampleCore := by
    unfold planeRatio exampleCore
    positivity
  have hr : radiusMinus n θ exampleCore ≤ 54 / 1000 := by
    have hθz := mul_le_mul hθhi hz (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 528 / 1000)
    unfold radiusMinus exampleCore
    change 2 * (28 / 10) * √(θ * (1 - θ) / n) + 2 * θ * √((75 / 10) / n) ≤ 54 / 1000
    nlinarith
  have hrp : radiusPlus n θ exampleCore ≤ 55 / 1000 := by
    have hθn : θ / (n : ℝ) ≤ (528 / 1000) / 11883 := by
      rw [div_le_div_iff₀ hn0 (by norm_num)]
      nlinarith
    unfold radiusPlus exampleCore
    change radiusMinus n θ exampleCore + 2 * θ * (75 / 10) / n ≤ 55 / 1000
    have he : 2 * θ * (75 / 10) / (n : ℝ) = 15 * (θ / n) := by ring
    rw [he]
    nlinarith
  exact ⟨hr, hrp⟩

end BstLean.Part235
