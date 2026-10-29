import BstLean.Part165Ev
import BstLean.Part187R143HidC
import BstLean.Part187R143HidC2
import BstLean.Part187R153PPs4
import BstLean.Part187R153Final
import BstLean.Part187R154C16
import BstLean.Part187R154NumA16
import BstLean.Part187R154NumB16
import BstLean.Part187R154Num16
import BstLean.Part187R160Event
import BstLean.Part187R160Cov
import BstLean.Part187R160Cov8

/-! Part 187 (file `Part187R165Ev`): copy of `Part165Ev` re-proved at the floor `16250 ≤ n` (was `16384 ≤ n`).
Only the declarations with the floor (and private helpers they use) are copied, in the nested
namespace `….R`. -/



namespace BstLean.Part165.R

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part150 (rhoC thetaC)
open BstLean.Part152 (opN)
open BstLean.Part153 (nuA jS)
open BstLean.Part160 (WqN XqN SXqN AgFam markov_XqN WqN_le exp_neg_13_le)

variable {n : ℕ}

/-- **The charge of `SXqN n 20`**: at most `5·10⁻⁵` (`n ≥ 16250`, `τ > 0`; `P' = 10`, so the
weight moment has order `2·20·10 = 400`, as in Part 160). -/
theorem SX20_charge (hn : 16250 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ SXqN n 20} ≤ 5 / 100000 := by
  have e : {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      ((c, τ), θ) ∉ SXqN n 20} =
      {θ | (1157 / 1000 * (n : ℝ)) ^ 20 * WqN 20 c τ < XqN 20 θ.1 θ.2 c τ} := by
    ext θ
    change ¬ (XqN 20 θ.1 θ.2 c τ ≤ (1157 / 1000 * (n : ℝ)) ^ 20 * WqN 20 c τ) ↔ _
    exact not_le
  rw [e]
  have h := markov_XqN (n := n) (q := 20) (P' := 10) (by norm_num) (by omega) c hτ
    (BstLean.Part153.jS_nonneg n 200 (6 / 1000))
    (fun _ hx => by
      exact BstLean.Part153.lemmaPP_i_sharp (by omega) (by norm_num)
        (by norm_num : (0 : ℝ) ≤ 6 / 1000) hx) (M := 1157 / 1000) (by norm_num)
  refine h.trans ?_
  have hj0 := BstLean.Part153.jS_nonneg n 200 (6 / 1000)
  have hj := BstLean.Part153.R.jS_200_le_16250 hn
  have hj2 : jS n 200 (6 / 1000) ^ 2 ≤ (10491 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hj0 hj 2
  have hratio : jS n 200 (6 / 1000) ^ 2 / (1157 / 1000) ≤ 9513 / 10000 := by
    rw [div_le_iff₀ (by norm_num)]
    refine hj2.trans (by norm_num)
  exact (pow_le_pow_left₀ (by positivity) hratio 200).trans BstLean.Part160.R.pow_9513_le

end BstLean.Part165.R
