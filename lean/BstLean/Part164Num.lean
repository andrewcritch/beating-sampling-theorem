import BstLean.Part164Bnd

/-!
# Part 164 (file `Num`): decimal bounds of the two constants

No proof is left open; no `native_decide` or `axiom` is used.

* `CAn_le`: `CAn n ≤ 1.532` for `n ≥ 23 000` (the paper's `nγ_A e_b χ_A⁺ = 2e_bχ_A⁺` with
  `e_b ≤ 0.7315`).
* `E0_le`: `E0 n ≤ 4.06·√(2/n) = 4.06·√γ_A` for `n ≥ 23 000` (the paper's `‖σ‖₈ ≤ (1 + H₁₆)√γ_A`
  has the factor `1.0013` in place of `4.06`).
-/

namespace BstLean.Part164

open Real
open BstLean.Part130

variable {n : ℕ}

theorem CAn_le (hn : 23000 ≤ n) : CAn n ≤ 1532 / 1000 := by
  unfold CAn chiUp
  have hnR : (23000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set s := √((n : ℝ) * 12) with hs
  have hs2 : s ^ 2 = (n : ℝ) * 12 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsl : (525 : ℝ) ≤ s := by
    rw [hs]
    calc (525 : ℝ) = √(525 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ √((n : ℝ) * 12) := Real.sqrt_le_sqrt (by nlinarith)
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hn0]
  nlinarith

theorem E0_le (hn : 23000 ≤ n) : E0 n ≤ 406 / 100 * √(2 / (n : ℝ)) := by
  unfold E0
  have hnR : (23000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hm : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have hsq : √(2 / ((mA n : ℕ) : ℝ)) * √(2 / ((mA n : ℕ) : ℝ)) = 2 / (n : ℝ) ^ 2 := by
    rw [Real.mul_self_sqrt (by positivity), hm]
  set r := √(n : ℝ) with hr
  have hr2 : r ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrl : (151 : ℝ) ≤ r := by
    rw [hr]
    calc (151 : ℝ) = √(151 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ √(n : ℝ) := Real.sqrt_le_sqrt (by nlinarith)
  have e : √(2 / ((mA n : ℕ) : ℝ)) * (√(2 / ((mA n : ℕ) : ℝ)) * (2 * (n : ℝ) + 5)) *
      (√(2 / (n : ℝ)) * ((n : ℝ) + 2 * r)) =
      √(2 / (n : ℝ)) * (2 / (n : ℝ) ^ 2 * ((2 * (n : ℝ) + 5) * ((n : ℝ) + 2 * r))) := by
    rw [← hsq]; ring
  rw [e, mul_comm (406 / 100 : ℝ)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  rw [← hr2]
  have a1 : (106 / 100 : ℝ) ≤ 6 / 100 * r - 8 := by linarith
  have a2 : r ^ 2 * (106 / 100) ≤ r ^ 2 * (6 / 100 * r - 8) :=
    mul_le_mul_of_nonneg_left a1 (sq_nonneg r)
  have a3 : 10 * r + 20 ≤ 106 / 100 * r ^ 2 := by nlinarith
  have a4 : 0 ≤ r ^ 2 * (6 / 100 * r - 8) - 10 * r - 20 := by linarith
  have a5 : 0 ≤ r * (r ^ 2 * (6 / 100 * r - 8) - 10 * r - 20) := mul_nonneg hr0 a4
  nlinarith

end BstLean.Part164
