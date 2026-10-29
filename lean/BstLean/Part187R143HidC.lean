import BstLean.Part143HidC

/-! Part 187 (file `Part187R143HidC`): copy of `Part143HidC` re-proved at the floor `16250 ≤ n` (was `16384 ≤ n`).
Only the declarations with the floor (and private helpers they use) are copied, in the nested
namespace `….R`. -/



namespace BstLean.Part143.R

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere)
open BstLean.Part105 (sphere_cont_integrable)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part140

variable {N m : ℕ}

/-- `n²/mW n ≤ 1/(127n)` for `n ≥ 16250`. -/
lemma nsq_div_mW_le128 {n : ℕ} (hn : 16250 ≤ n) :
    (n : ℝ) ^ 2 / (mW n : ℝ) ≤ 1 / (127 * (n : ℝ)) := by
  have hn' : (16250 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  refine ratio_le (n0 := n) (by omega) le_rfl (by positivity) ?_
  rw [div_pow, one_pow, mul_pow]
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (n : ℝ), mul_pos hnpos hnpos]

end BstLean.Part143.R

