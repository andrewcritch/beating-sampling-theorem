import BstLean.Part223Tail

/-! A symbolic comparison with the paper's order256 coefficient on the frontier range. -/
namespace BstLean.Part223
open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part170 (tA mkR)
open BstLean.Part212 (exactRadius)
open BstLean.Part152 (gaussMomConst gaussMomConst_nonneg)
open BstLean.Part220

lemma rowMaximumFactor_frontier {n : ℕ} (hn : n ≤ 16384) :
    (mA n : ℝ) ^ (1 / (256 : ℝ)) ≤ 10 / 9 := by
  have hnR : (n : ℝ) ≤ 16384 := by exact_mod_cast hn
  rw [one_div]
  apply (rpow_inv_le_iff_of_pos (Nat.cast_nonneg _) (by norm_num)
    (by norm_num : (0 : ℝ) < 256)).mpr
  rw [show (256 : ℝ) = (256 : ℕ) by norm_num, rpow_natCast]
  calc
    (mA n : ℝ) = (n : ℝ) ^ 2 := by simp [mA]
    _ ≤ (16384 : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hnR 2
    _ ≤ (10 / 9 : ℝ) ^ 256 := by norm_num

lemma maximumFactor_le_paperSquare {n : ℕ} (hn : 8000 ≤ n) (hn' : n ≤ 16384) :
    (mA n : ℝ) ^ (1 / (256 : ℝ)) * ((n - 1 - 1 : ℕ) + (512 : ℝ)) ≤
      (sqrt (n : ℝ) + paperT0 n + paperTail256 n) ^ 2 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnR' : (n : ℝ) ≤ 16384 := by exact_mod_cast hn'
  have hd : ((n - 1 - 1 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    have he : n - 1 - 1 = n - 2 := by omega
    rw [he, Nat.cast_sub (by omega)]
    norm_num
  have hd' : ((n - 1 - 1 : ℕ) : ℝ) + 512 ≤ 107 / 100 * (n : ℝ) := by
    rw [hd]
    linarith
  have hs : sqrt (n : ℝ) ≤ 128 := sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  have hs0 := sqrt_nonneg (n : ℝ)
  have hsq := sq_sqrt (Nat.cast_nonneg n)
  have hm := mul_le_mul_of_nonneg_left hs hs0
  have ht := (paperT0_bounds hn hn').1
  have htail := paperTail256_lower hn hn'
  calc
    _ ≤ (10 / 9 : ℝ) * (107 / 100 * (n : ℝ)) :=
      mul_le_mul (rowMaximumFactor_frontier hn') hd' (by positivity) (by norm_num)
    _ ≤ 6 / 5 * (n : ℝ) := by nlinarith
    _ ≤ (sqrt (n : ℝ) + 13) ^ 2 := by nlinarith
    _ ≤ (sqrt (n : ℝ) + paperT0 n + paperTail256 n) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2

#print axioms rowMaximumFactor_frontier
#print axioms maximumFactor_le_paperSquare
end BstLean.Part223
