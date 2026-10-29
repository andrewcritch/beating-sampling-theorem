import BstLean.Part201Windows

/-! Part 201: the computed sphere constant satisfies the existing `ConstC` definition. -/

namespace BstLean.Part201
open Real
open BstLean.Part130 BstLean.Part159
open BstLean.Part137 (cN)
open BstLean.Part141 (cN_nonneg)
open BstLean.Part157 (cNt)

theorem constC {n : ℕ} (hn : 4096 ≤ n) : ConstC n := by
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hc := cNt_close (n := n) (by omega)
  obtain ⟨-, hcw⟩ := cN_even_window hn
  have hc0 := cN_nonneg (2 * n)
  have hm : mW n ≤ n ^ 4 := by
    rw [mW_le_iff]
    calc n ^ 7 ≤ n ^ 7 * n := Nat.le_mul_of_pos_right _ (by omega)
      _ = (n ^ 4) ^ 2 := by ring
  have hm' : (mW n : ℝ) ≤ (n : ℝ) ^ 4 := by exact_mod_cast hm
  have hsq : (cNt n - cN (2 * n)) ^ 2 ≤ (cN (2 * n) / (3 * 10 ^ 23 * (n : ℝ) ^ 2)) ^ 2 := by
    rw [← sq_abs (cNt n - cN (2 * n))]
    exact pow_le_pow_left₀ (abs_nonneg _) hc 2
  have hsq2 : (cN (2 * n) / (3 * 10 ^ 23 * (n : ℝ) ^ 2)) ^ 2 ≤
      8 / (100 * (n : ℝ)) / (3 * 10 ^ 23 * (n : ℝ) ^ 2) ^ 2 := by
    rw [div_pow]
    exact div_le_div_of_nonneg_right hcw (by positivity)
  unfold ConstC
  have h1 : (cNt n - cN (2 * n)) ^ 2 * (n : ℝ) * (mW n : ℝ) ≤
      8 / (100 * (n : ℝ)) / (3 * 10 ^ 23 * (n : ℝ) ^ 2) ^ 2 * (n : ℝ) * (n : ℝ) ^ 4 :=
    mul_le_mul (mul_le_mul_of_nonneg_right (hsq.trans hsq2) hnpos.le) hm' (Nat.cast_nonneg _)
      (by positivity)
  refine h1.trans (le_of_eq_of_le ?_ ?_ (b := (8 : ℝ) / (100 * 9 * 10 ^ 46)))
  · field_simp
    norm_num
  · norm_num


end BstLean.Part201
#print axioms BstLean.Part201.constC
