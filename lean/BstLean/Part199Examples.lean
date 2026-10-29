import BstLean.Part199Geometry

/-! Part 199: a nonempty analytic window throughout the frontier dimension interval.
This certificate concerns geometry only. It supplies no small TI constant. -/
namespace BstLean.Part199
open Real

def exampleWide : Window := ⟨6, 20, 8, by norm_num, by norm_num, by norm_num⟩

noncomputable def exampleCore : Window := ⟨28 / 10, 75 / 10, 32 / 10,
  by norm_num, by norm_num, by norm_num⟩

theorem example_nested : exampleCore.LE exampleWide := by
  norm_num [Window.LE, exampleCore, exampleWide]

theorem example_overlap_guard {n : ℕ} (hn : 4096 ≤ n) {θ : ℝ}
    (hθlo : 46 / 100 ≤ θ) (hθhi : θ ≤ 528 / 1000) :
    OverlapGuard n θ exampleWide (1 / 4) (9 / 10) := by
  have hnR : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0 : 0 ≤ θ := by linarith
  have h1θ : 0 < 1 - θ := by linarith
  have hs : (64 : ℝ) ≤ √(n : ℝ) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hs0 : 0 < √(n : ℝ) := by linarith
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg n)
  have ha : √(θ * (1 - θ) / n) ≤ 1 / 128 := by
    apply BstLean.Part182.sqrt_le_of_sq' (by norm_num)
    rw [div_le_iff₀ hn0]
    nlinarith [sq_nonneg (θ - 1 / 2)]
  have hz : √((20 : ℝ) / n) ≤ 7 / 100 := by
    apply BstLean.Part182.sqrt_le_of_sq' (by norm_num)
    rw [div_le_iff₀ hn0]
    nlinarith
  have hb : planeRatio n θ exampleWide ≤ 1 / 10 := by
    unfold planeRatio exampleWide
    change 6 * √(θ / ((1 - θ) * n)) ≤ 1 / 10
    have hroot : √(θ / ((1 - θ) * n)) ≤ 1 / 60 := by
      apply BstLean.Part182.sqrt_le_of_sq' (by norm_num)
      rw [div_le_iff₀ (mul_pos h1θ hn0)]
      have hmul := mul_le_mul_of_nonneg_left hnR h1θ.le
      nlinarith
    linarith
  have hb0 : 0 ≤ planeRatio n θ exampleWide := by
    unfold planeRatio exampleWide
    positivity
  have hr : radiusMinus n θ exampleWide ≤ 17 / 100 := by
    have hθz := mul_le_mul hθhi hz (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 528 / 1000)
    unfold radiusMinus exampleWide
    change 2 * 6 * √(θ * (1 - θ) / n) + 2 * θ * √(20 / n) ≤ 17 / 100
    nlinarith
  have hrp : radiusPlus n θ exampleWide ≤ 18 / 100 := by
    have hθn : θ / (n : ℝ) ≤ (528 / 1000) / 4096 := by
      rw [div_le_div_iff₀ hn0 (by norm_num)]
      nlinarith
    unfold radiusPlus exampleWide
    change radiusMinus n θ exampleWide + 2 * θ * 20 / n ≤ 18 / 100
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
  have hgn : BstLean.Part182.gPlus n 20 / (n : ℝ) ≤ 1 / 64 + 5 / 4096 := by
    have hsn : √(n : ℝ) / (n : ℝ) ≤ 1 / 64 := by
      rw [div_le_iff₀ hn0]
      nlinarith
    have h5n : (5 : ℝ) / n ≤ 5 / 4096 := by
      rw [div_le_iff₀ hn0]
      nlinarith
    have h := div_le_div_of_nonneg_right hg hn0.le
    rw [add_div] at h
    linarith
  have hterm : θ / (n : ℝ) * 8 * BstLean.Part182.gPlus n 20 ≤ 72 / 1000 := by
    have hg0 : 0 ≤ BstLean.Part182.gPlus n 20 / (n : ℝ) := by
      unfold BstLean.Part182.gPlus
      positivity
    have hm := mul_le_mul hθhi hgn hg0 (by norm_num : (0 : ℝ) ≤ 528 / 1000)
    have he : θ / (n : ℝ) * 8 * BstLean.Part182.gPlus n 20 =
        8 * (θ * (BstLean.Part182.gPlus n 20 / (n : ℝ))) := by ring
    rw [he]
    nlinarith
  have hupper : (1 - θ) * (1 + planeRatio n θ exampleWide) ^ 2 ≤ (54 / 100) * (11 / 10) ^ 2 := by
    apply mul_le_mul (by linarith : 1 - θ ≤ 54 / 100)
      (pow_le_pow_left₀ (by linarith) (by linarith : 1 + planeRatio n θ exampleWide ≤ 11 / 10) 2)
      (by positivity) (by norm_num)
  have hlower : (472 / 1000) * (9 / 10) ^ 2 ≤ (1 - θ) * (1 - planeRatio n θ exampleWide) ^ 2 := by
    apply mul_le_mul (by linarith : 472 / 1000 ≤ 1 - θ)
      (pow_le_pow_left₀ (by norm_num) (by linarith : 9 / 10 ≤ 1 - planeRatio n θ exampleWide) 2)
      (by positivity) h1θ.le
  refine ⟨hθ0, by linarith, by linarith, by linarith, by norm_num, ?_, ?_⟩
  · unfold overlapNumerator
    simp only [neg_one_mul, sub_eq_add_neg]
    change 1 / 4 * (1 + radiusPlus n θ exampleWide) ≤
      (1 - θ) * (1 - planeRatio n θ exampleWide) ^ 2 - θ / n * 8 * BstLean.Part182.gPlus n 20
    nlinarith
  · unfold overlapNumerator
    simp only [one_mul]
    change (1 - θ) * (1 + planeRatio n θ exampleWide) ^ 2 +
      θ / n * 8 * BstLean.Part182.gPlus n 20 ≤ 9 / 10 * (1 - radiusMinus n θ exampleWide)
    nlinarith

/-- A false positive-radius guard cannot enter an overlap certificate. -/
theorem radius_guard_rejected {n : ℕ} {θ lo hi : ℝ} {w : Window}
    (h : 1 ≤ radiusMinus n θ w) : ¬ OverlapGuard n θ w lo hi := by
  intro hg
  exact (not_lt_of_ge h) hg.radius_lt_one

/-- The broad checked interval contains actual core pairs at every frontier dimension. -/
theorem example_core_overlap {n : ℕ} (hn : 4096 ≤ n) {c : Fin n → ℝ} {τ : ℝ}
    (hτ : 0 < τ) (hθlo : 46 / 100 ≤ BstLean.Part150.thetaC c τ)
    (hθhi : BstLean.Part150.thetaC c τ ≤ 528 / 1000)
    {a b : Fin n → ℝ}
    (hp : (a, b) ∈ BstLean.Part182.GammaS c exampleCore.t exampleCore.z exampleCore.pair) :
    1 / 4 ≤ dotProduct (BstLean.Part130.sphPt (c + τ • a))
      (BstLean.Part130.sphPt (c + τ • b)) ∧
    dotProduct (BstLean.Part130.sphPt (c + τ • a))
      (BstLean.Part130.sphPt (c + τ • b)) ≤ 9 / 10 := by
  exact overlap_of_guard (by omega) hτ exampleWide (example_overlap_guard hn hθlo hθhi)
    (gamma_subset c example_nested hp)

end BstLean.Part199
