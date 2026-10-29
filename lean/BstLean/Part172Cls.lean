import BstLean.Part172Mom

/-!
# Part 172 (file `Cls`): numerical bounds of the LS constants `c_q`

No proof is left open; no `native_decide` or `axiom` is used.

`cLS q = (π/2)·(E|g|^{2q})^{1/(2q)}`: `cLS 2 ≤ 2.0674`, `cLS 4 ≤ 2.8115`, `cLS 8 ≤ 3.8967`.
-/

namespace BstLean.Part172

open Real BstLean.Part162

lemma cl_rpow_le {x b : ℝ} {k : ℕ} (hk : 0 < k) (hx : 0 ≤ x) (hb : 0 ≤ b) (h : x ≤ b ^ k) :
    x ^ ((k : ℝ)⁻¹) ≤ b := by
  calc x ^ ((k : ℝ)⁻¹) ≤ (b ^ k) ^ ((k : ℝ)⁻¹) :=
        Real.rpow_le_rpow hx h (by positivity)
    _ = b := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hb, mul_inv_cancel₀ (by positivity),
          Real.rpow_one]

lemma cl_gmom (k : ℕ) : gmom (2 * k) = ∏ j ∈ Finset.range k, (2 * j + 1 : ℝ) := gmom_even k

lemma cl_pi : π / 2 ≤ 15708 / 10000 := by
  have := Real.pi_lt_d4; linarith

lemma cLS2_le : cLS 2 ≤ 20674 / 10000 := by
  unfold cLS
  have hg : gmom (2 * 2) = 3 := by rw [cl_gmom]; norm_num [Finset.prod_range_succ]
  have h1 : gmom (2 * 2) ^ (((2 * 2 : ℕ) : ℝ)⁻¹) ≤ 13161 / 10000 :=
    cl_rpow_le (by norm_num) (by rw [hg]; norm_num) (by norm_num) (by rw [hg]; norm_num)
  calc π / 2 * gmom (2 * 2) ^ (((2 * 2 : ℕ) : ℝ)⁻¹) ≤ 15708 / 10000 * (13161 / 10000) := by
        exact mul_le_mul cl_pi h1 (Real.rpow_nonneg (by rw [cl_gmom]; positivity) _) (by norm_num)
    _ ≤ _ := by norm_num

lemma cLS4_le : cLS 4 ≤ 28115 / 10000 := by
  unfold cLS
  have hg : gmom (2 * 4) = 105 := by rw [cl_gmom]; norm_num [Finset.prod_range_succ]
  have h1 : gmom (2 * 4) ^ (((2 * 4 : ℕ) : ℝ)⁻¹) ≤ 17898 / 10000 :=
    cl_rpow_le (by norm_num) (by rw [hg]; norm_num) (by norm_num) (by rw [hg]; norm_num)
  calc π / 2 * gmom (2 * 4) ^ (((2 * 4 : ℕ) : ℝ)⁻¹) ≤ 15708 / 10000 * (17898 / 10000) := by
        exact mul_le_mul cl_pi h1 (Real.rpow_nonneg (by rw [cl_gmom]; positivity) _) (by norm_num)
    _ ≤ _ := by norm_num

lemma cLS8_le : cLS 8 ≤ 38967 / 10000 := by
  unfold cLS
  have hg : gmom (2 * 8) = 2027025 := by rw [cl_gmom]; norm_num [Finset.prod_range_succ]
  have h1 : gmom (2 * 8) ^ (((2 * 8 : ℕ) : ℝ)⁻¹) ≤ 24806 / 10000 :=
    cl_rpow_le (by norm_num) (by rw [hg]; norm_num) (by norm_num) (by rw [hg]; norm_num)
  calc π / 2 * gmom (2 * 8) ^ (((2 * 8 : ℕ) : ℝ)⁻¹) ≤ 15708 / 10000 * (24806 / 10000) := by
        exact mul_le_mul cl_pi h1 (Real.rpow_nonneg (by rw [cl_gmom]; positivity) _) (by norm_num)
    _ ≤ _ := by norm_num

end BstLean.Part172
