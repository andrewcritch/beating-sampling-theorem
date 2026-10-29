import BstLean.Part153PPs4
import BstLean.Part187R143HidC
import BstLean.Part187R143HidC2

/-! Part 187 (file `Part187R153PPs4`): copy of `Part153PPs4` re-proved at the floor `16250 ≤ n` (was `16384 ≤ n`).
Only the declarations with the floor (and private helpers they use) are copied, in the nested
namespace `….R`. -/



namespace BstLean.Part153.R

open MeasureTheory ProbabilityTheory Real Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part148 (EuLip)
open BstLean.Part130 BstLean.Part152
open BstLean.Part151 (jac mask)


set_option maxRecDepth 100000 in
set_option exponentiation.threshold 1000 in
/-- `jS n 200 (6/1000) ≤ 1.0491` for `n ≥ 16250`. -/
lemma jS_200_le_16250 {n : ℕ} (hn : 16250 ≤ n) : jS n 200 (6 / 1000) ≤ 10491 / 10000 := by
  have hnr : (16250 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs : (127 : ℝ) ≤ √(n : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    linarith
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have hg0 := gaussMomConst_nonneg 200
  have hg := gaussMomConst_200_le
  have hu : 1 / √(n : ℝ) ≤ 1 / 127 := one_div_le_one_div_of_le (by norm_num) hs
  have hw : gaussMomConst 200 / (n : ℝ) ≤ (25 / 2) / 16250 := by
    rw [div_le_div_iff₀ hn0 (by norm_num)]
    nlinarith
  have hgu : gaussMomConst 200 / √(n : ℝ) ≤ (25 / 2) / 127 := by
    rw [div_le_div_iff₀ hs0 (by norm_num)]
    nlinarith
  refine (jS_le_atoms n 200 (6 / 1000) sqrt_two_le sqrt_eta_le hu hw hgu
    (epsS_200_le (by omega))).trans ?_
  norm_num


set_option exponentiation.threshold 1000 in
/-- **Lemma PP, numeric corollary with the paper's `M_P` at `n = 16250`** (`P = 200`,
`η = 6/1000`): for `n ≥ 16250`, `Pr(Ξ₄ > (11911/10000)·γ_A/n) ≤ 5·10⁻⁵`. -/
theorem lemmaPP_numeric_16250 {n : ℕ} (hn : 16250 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA n).real {θ | (11911 / 10000 : ℝ) * (2 / (n : ℝ)) / n < Xi4 θ.1 θ.2 c τ} ≤
      5 / 100000 := by
  have hnr : (16250 : ℝ) ≤ n := by exact_mod_cast hn
  refine lemmaPP_numeric_aux (by omega) c hτ (by norm_num) (jS_200_le_16250 hn) ?_
  norm_num
  linarith


section cov

variable {n : ℕ}

end cov

end BstLean.Part153.R

