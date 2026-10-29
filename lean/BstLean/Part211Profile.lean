import BstLean.Part211HS

/-! Equality between the nested-root HS profile and the paper's displayed profile. -/
namespace BstLean.Part211
open Real

noncomputable def a0 (n : ℕ) : ℝ :=
  2 * √24 / (√2 * √(n : ℝ) * √(√(n : ℝ)))

theorem hsProfile_eq_paper {n : ℕ} (hn : 1 ≤ n) {θ : ℝ} (hθ : 0 < θ) (v : ℝ) :
    hsProfile n θ v = (√(√(BstLean.Part194.CH n θ v)) + a0 n / √θ) ^ 4 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  let d := √(n : ℝ) * √(√(n : ℝ))
  let b := √2 * √θ / d
  have hd : 0 < d := by dsimp [d]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hd2 : d ^ 2 = (n : ℝ) * √(n : ℝ) := by
    dsimp [d]
    rw [mul_pow, sq_sqrt hnR.le, sq_sqrt (sqrt_nonneg _)]
  have hfour : ∀ x : ℝ, 0 ≤ x → (√x) ^ 4 = x ^ 2 := by
    intro x hx
    rw [show (√x) ^ 4 = ((√x) ^ 2) ^ 2 by ring, sq_sqrt hx]
  have hd4 : d ^ 4 = (n : ℝ) ^ 3 := by
    rw [show d ^ 4 = (d ^ 2) ^ 2 by ring, hd2, mul_pow, sq_sqrt hnR.le]
    ring
  have hb4 : b ^ 4 = 4 * θ ^ 2 / (n : ℝ) ^ 3 := by
    dsimp [b]
    rw [div_pow, mul_pow, hfour 2 (by norm_num), hfour θ hθ.le, hd4]
    norm_num
  have hFirst : √(√(4 * θ ^ 2 / (n : ℝ) ^ 3 * BstLean.Part194.CH n θ v)) =
      b * √(√(BstLean.Part194.CH n θ v)) := by
    rw [← hb4, sqrt_mul (by positivity : 0 ≤ b ^ 4),
      show b ^ 4 = (b ^ 2) ^ 2 by ring, sqrt_sq (sq_nonneg _),
      sqrt_mul (sq_nonneg _), sqrt_sq hb.le]
  have hSecond : b * (a0 n / √θ) = 2 * √24 / ((n : ℝ) * √(n : ℝ)) := by
    have ha : a0 n = 2 * √24 / (√2 * d) := by unfold a0 d; ring
    rw [ha]
    calc b * ((2 * √24 / (√2 * d)) / √θ) = 2 * √24 / d ^ 2 := by
           dsimp [b]
           field_simp
         _ = _ := by rw [hd2]
  have hRoot : hsRoot n θ v = b * (√(√(BstLean.Part194.CH n θ v)) + a0 n / √θ) := by
    unfold hsRoot
    rw [hFirst, mul_add, hSecond]
  unfold hsProfile
  rw [hRoot, mul_pow, hb4]
  field_simp

#print axioms hsProfile_eq_paper
end BstLean.Part211
