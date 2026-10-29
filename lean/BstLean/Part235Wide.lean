import BstLean.Part235Geometry

/-! Part 235: checked wide geometry from dimension 11883. -/
namespace BstLean.Part235
open Real BstLean.Part199

theorem wide_overlap_guard {n : ℕ} (hn : 11883 ≤ n) {θ : ℝ}
    (hθlo : 46 / 100 ≤ θ) (hθhi : θ ≤ 528 / 1000) :
    OverlapGuard n θ exampleWide (34 / 100) (73 / 100) := by
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
  have hz : √((20 : ℝ) / n) ≤ 42 / 1000 := by
    apply BstLean.Part182.sqrt_le_of_sq' (by norm_num)
    rw [div_le_iff₀ hn0]
    nlinarith
  have hb : planeRatio n θ exampleWide ≤ 6 / 100 := by
    unfold planeRatio exampleWide
    change 6 * √(θ / ((1 - θ) * n)) ≤ 6 / 100
    have hroot : √(θ / ((1 - θ) * n)) ≤ 1 / 100 := by
      apply BstLean.Part182.sqrt_le_of_sq' (by norm_num)
      rw [div_le_iff₀ (mul_pos h1θ hn0)]
      have hmul := mul_le_mul_of_nonneg_left hnR h1θ.le
      nlinarith
    linarith
  have hb0 : 0 ≤ planeRatio n θ exampleWide := by
    unfold planeRatio exampleWide
    positivity
  have hr : radiusMinus n θ exampleWide ≤ 1 / 10 := by
    have hθz := mul_le_mul hθhi hz (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 528 / 1000)
    unfold radiusMinus exampleWide
    change 2 * 6 * √(θ * (1 - θ) / n) + 2 * θ * √(20 / n) ≤ 1 / 10
    nlinarith
  have hrp : radiusPlus n θ exampleWide ≤ 102 / 1000 := by
    have hθn : θ / (n : ℝ) ≤ (528 / 1000) / 11883 := by
      rw [div_le_div_iff₀ hn0 (by norm_num)]
      nlinarith
    unfold radiusPlus exampleWide
    change radiusMinus n θ exampleWide + 2 * θ * 20 / n ≤ 102 / 1000
    have he : 2 * θ * 20 / (n : ℝ) = 40 * (θ / n) := by ring
    rw [he]
    nlinarith
  have hg : BstLean.Part182.gPlus n 20 ≤ √(n : ℝ) + 5 := by
    apply BstLean.Part182.sqrt_le_of_sq' (by positivity)
    have h20 : √(20 : ℝ) ≤ 9 / 2 :=
      BstLean.Part182.sqrt_le_of_sq' (by norm_num) (by norm_num)
    have hm := mul_le_mul_of_nonneg_left h20 hs0.le
    rw [Real.sqrt_mul (Nat.cast_nonneg n)]
    nlinarith
  have hgn : BstLean.Part182.gPlus n 20 / (n : ℝ) ≤ 1 / 109 + 5 / 11883 := by
    have hsn : √(n : ℝ) / (n : ℝ) ≤ 1 / 109 := by
      rw [div_le_iff₀ hn0]
      nlinarith
    have h5n : (5 : ℝ) / n ≤ 5 / 11883 := by
      rw [div_le_iff₀ hn0]
      nlinarith
    have h := div_le_div_of_nonneg_right hg hn0.le
    rw [add_div] at h
    linarith
  have hterm : θ / (n : ℝ) * 8 * BstLean.Part182.gPlus n 20 ≤ 41 / 1000 := by
    have hg0 : 0 ≤ BstLean.Part182.gPlus n 20 / (n : ℝ) := by
      unfold BstLean.Part182.gPlus
      positivity
    have hm := mul_le_mul hθhi hgn hg0 (by norm_num : (0 : ℝ) ≤ 528 / 1000)
    have he : θ / (n : ℝ) * 8 * BstLean.Part182.gPlus n 20 =
        8 * (θ * (BstLean.Part182.gPlus n 20 / (n : ℝ))) := by ring
    rw [he]
    nlinarith
  have hupper : (1 - θ) * (1 + planeRatio n θ exampleWide) ^ 2 ≤ (54 / 100) * (106 / 100) ^ 2 := by
    apply mul_le_mul (by linarith : 1 - θ ≤ 54 / 100)
      (pow_le_pow_left₀ (by linarith) (by linarith : 1 + planeRatio n θ exampleWide ≤ 106 / 100) 2)
      (by positivity) (by norm_num)
  have hlower : (472 / 1000) * (94 / 100) ^ 2 ≤ (1 - θ) * (1 - planeRatio n θ exampleWide) ^ 2 := by
    apply mul_le_mul (by linarith : 472 / 1000 ≤ 1 - θ)
      (pow_le_pow_left₀ (by norm_num) (by linarith : 94 / 100 ≤ 1 - planeRatio n θ exampleWide) 2)
      (by positivity) h1θ.le
  refine ⟨hθ0, by linarith, by linarith, by linarith, by norm_num, ?_, ?_⟩
  · unfold overlapNumerator
    simp only [neg_one_mul, sub_eq_add_neg]
    change 34 / 100 * (1 + radiusPlus n θ exampleWide) ≤
      (1 - θ) * (1 - planeRatio n θ exampleWide) ^ 2 - θ / n * 8 * BstLean.Part182.gPlus n 20
    nlinarith
  · unfold overlapNumerator
    simp only [one_mul]
    change (1 - θ) * (1 + planeRatio n θ exampleWide) ^ 2 +
      θ / n * 8 * BstLean.Part182.gPlus n 20 ≤ 73 / 100 * (1 - radiusMinus n θ exampleWide)
    nlinarith


/-- The exact radius formulas have uniform rational upper bounds. -/
theorem wide_radius_caps {n : ℕ} (hn : 11883 ≤ n) {θ : ℝ}
    (hθlo : 46 / 100 ≤ θ) (hθhi : θ ≤ 528 / 1000) :
    radiusMinus n θ exampleWide ≤ 1 / 10 ∧ radiusPlus n θ exampleWide ≤ 102 / 1000 := by
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
  have hz : √((20 : ℝ) / n) ≤ 42 / 1000 := by
    apply BstLean.Part182.sqrt_le_of_sq' (by norm_num)
    rw [div_le_iff₀ hn0]
    nlinarith
  have hb : planeRatio n θ exampleWide ≤ 6 / 100 := by
    unfold planeRatio exampleWide
    change 6 * √(θ / ((1 - θ) * n)) ≤ 6 / 100
    have hroot : √(θ / ((1 - θ) * n)) ≤ 1 / 100 := by
      apply BstLean.Part182.sqrt_le_of_sq' (by norm_num)
      rw [div_le_iff₀ (mul_pos h1θ hn0)]
      have hmul := mul_le_mul_of_nonneg_left hnR h1θ.le
      nlinarith
    linarith
  have hb0 : 0 ≤ planeRatio n θ exampleWide := by
    unfold planeRatio exampleWide
    positivity
  have hr : radiusMinus n θ exampleWide ≤ 1 / 10 := by
    have hθz := mul_le_mul hθhi hz (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 528 / 1000)
    unfold radiusMinus exampleWide
    change 2 * 6 * √(θ * (1 - θ) / n) + 2 * θ * √(20 / n) ≤ 1 / 10
    nlinarith
  have hrp : radiusPlus n θ exampleWide ≤ 102 / 1000 := by
    have hθn : θ / (n : ℝ) ≤ (528 / 1000) / 11883 := by
      rw [div_le_div_iff₀ hn0 (by norm_num)]
      nlinarith
    unfold radiusPlus exampleWide
    change radiusMinus n θ exampleWide + 2 * θ * 20 / n ≤ 102 / 1000
    have he : 2 * θ * 20 / (n : ℝ) = 40 * (θ / n) := by ring
    rw [he]
    nlinarith
  exact ⟨hr, hrp⟩

end BstLean.Part235
