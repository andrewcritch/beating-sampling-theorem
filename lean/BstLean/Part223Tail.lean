import BstLean.Part223Arithmetic

/-! A symbolic comparison with the paper's order256 coefficient on the frontier range. -/
namespace BstLean.Part223
open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part170 (tA mkR)
open BstLean.Part212 (exactRadius)
open BstLean.Part152 (gaussMomConst gaussMomConst_nonneg)
open BstLean.Part220

lemma root256_lower {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ (256 : ℕ) ≤ b) :
    a ≤ b ^ (1 / (256 : ℝ)) := by
  rw [one_div]
  apply (le_rpow_inv_iff_of_pos ha hb (by norm_num : (0 : ℝ) < 256)).mpr
  convert h using 1
  exact rpow_natCast a 256

lemma paperTail256_lower {n : ℕ} (hn : 8000 ≤ n) (hn' : n ≤ 16384) :
    8 ≤ paperTail256 n := by
  have ht := paperT0_bounds hn hn'
  have hgm : (8 : ℝ) ≤ gaussMomConst 128 := by
    change (8 : ℝ) ≤ ((2 : ℝ) ^ 128 * ((128 : ℕ).factorial : ℝ)) ^ (1 / (256 : ℝ))
    apply root256_lower (by norm_num)
      (mul_nonneg (pow_nonneg (by norm_num) 128) (Nat.cast_nonneg _))
    exact_mod_cast gaussian_factorial_lower
  have hf : (64 : ℝ) ≤ ((256 : ℕ).factorial : ℝ) ^ (1 / (256 : ℝ)) := by
    apply root256_lower (by norm_num) (Nat.cast_nonneg _)
    exact_mod_cast factorial256_lower
  apply le_min hgm
  rw [le_div_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 5) ht.1)]
  calc
    (8 : ℝ) * paperT0 n ≤ 8 * 8 := mul_le_mul_of_nonneg_left ht.2 (by norm_num)
    _ ≤ ((256 : ℕ).factorial : ℝ) ^ (1 / (256 : ℝ)) := by
      simpa only [show (8 : ℝ) * 8 = 64 by norm_num] using hf

#print axioms root256_lower
#print axioms paperTail256_lower
end BstLean.Part223
