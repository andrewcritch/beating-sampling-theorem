import BstLean.Part165End

/-!
# Part 165 (file `Num`): a decimal value of the mass bound

No proof is left open; no `native_decide` or `axiom` is used.

* `gmom_40`: `E g⁴⁰ = 39!! = 319 830 986 772 877 770 815 625`.
* **`betaM_043`**: `betaM n 0.43 ≤ 2·10⁻¹⁵` for `n ≥ 23 000` (floor `d_low = 0.43² = 0.1849`).
-/

namespace BstLean.Part165

open Real
open BstLean.Part162 (gmom gmom_even)

lemma gmom_40 : gmom 40 = 319830986772877770815625 := by
  have h := gmom_even 20
  norm_num [Finset.prod_range_succ] at h
  exact h

/-- **The mass bound at the floor `sd = 0.43`**: `betaM n 0.43 ≤ 2·10⁻¹⁵` (`n ≥ 23 000`). -/
theorem betaM_043 {n : ℕ} (hn : 23000 ≤ n) : betaM n (43 / 100) ≤ 2 / 10 ^ 15 := by
  have hnR : (23000 : ℝ) ≤ n := by exact_mod_cast hn
  unfold betaM s0
  rw [gmom_40]
  have hpi : π / 2 ≤ 15708 / 10000 := by have := Real.pi_lt_d4; linarith
  have h1 : (π / 2) ^ 40 ≤ (15708 / 10000 : ℝ) ^ 40 :=
    pow_le_pow_left₀ (by positivity) hpi 40
  have h2 : 706 / 1000 / ((n : ℝ) * (5087 / 10000 - 43 / 100) ^ 2) ≤
      706 / 1000 / ((23000 : ℝ) * (5087 / 10000 - 43 / 100) ^ 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right hnR (by norm_num))
  have h3 := pow_le_pow_left₀ (by positivity) h2 20
  calc (π / 2) ^ 40 * 319830986772877770815625 *
        (706 / 1000 / ((n : ℝ) * (5087 / 10000 - 43 / 100) ^ 2)) ^ 20
      ≤ (15708 / 10000 : ℝ) ^ 40 * 319830986772877770815625 *
        (706 / 1000 / ((23000 : ℝ) * (5087 / 10000 - 43 / 100) ^ 2)) ^ 20 :=
        mul_le_mul (mul_le_mul_of_nonneg_right h1 (by norm_num)) h3 (by positivity)
          (by positivity)
    _ ≤ 2 / 10 ^ 15 := by norm_num

end BstLean.Part165
